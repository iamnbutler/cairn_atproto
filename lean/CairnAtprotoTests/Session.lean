import CairnAtproto

open CairnJson CairnAtproto CairnAtproto.Session

/-! Runs of the session machine against scripted replies. -/

def host := "https://bsky.social"
def pds := "https://pds.example.com"
def sessionBody : ByteArray :=
  ("{\"accessJwt\":\"\",\"refreshJwt\":\"\",\"did\":\"did:plc:alice\",\"handle\":\"alice.test\"," ++
   "\"didDoc\":{\"service\":[{\"id\":\"#atproto_pds\",\"serviceEndpoint\":\"" ++ pds ++ "\"}]}}").toUTF8
def okSession : Cairn.Reply := .http 200 [] sessionBody
def expired : Cairn.Reply := .http 400 [] "{\"error\":\"ExpiredToken\",\"message\":\"Token has expired\"}".toUTF8
def invalid : Cairn.Reply := .http 400 [] "{\"error\":\"InvalidToken\"}".toUTF8
def ok : Cairn.Reply := .http 200 [] "{\"feed\":[]}".toUTF8
def alice : Account := { did := "did:plc:alice", handle := "alice.test", service := pds }

def sends (o : List Out) : List (Nat × Kind × String × Option String) :=
  o.filterMap fun | .send rid k h => some (rid, k, urlOf h, itemOf h) | _ => none
def cancels (o : List Out) : List Nat := o.filterMap fun | .cancel rid => some rid | _ => none
def forgets (o : List Out) : List String := o.filterMap fun | .forget _ i => some i | _ => none
def answers (o : List Out) : List (Nat × Bool) :=
  o.filterMap fun | .answer id (.reply _) => some (id, true) | .answer id .signedOut => some (id, false) | _ => none

-- Sign in: the one createSession, redacted, capturing both tokens, no secret.
def s1 := step init (.signIn host "alice.test" "app-password")
#guard s1.1.phase == .signingIn 0 host
#guard sends s1.2 == [(0, .signIn, host ++ "/xrpc/com.atproto.server.createSession", none)]
#guard s1.2.all fun | .send _ _ h => h.redact | _ => true
-- The password is in no state.
#guard !(reprStr s1.1).contains "app-password"

-- Its reply: signed in, calls go to the PDS from the DID document.
def s2 := step s1.1 (.reply 0 okSession)
#guard s2.1.phase == .signedIn alice
def s3 := step s2.1 (.call 7 (.getTimeline (some 50) none))
#guard sends s3.2 == [(1, .call 0, pds ++ "/xrpc/app.bsky.feed.getTimeline?limit=50", some "access")]

-- ExpiredToken: one refresh, the call held; a second call joins it; a stray reply changes nothing.
def s4 := step s3.1 (.reply 1 expired)
#guard s4.1.phase == .refreshing 2 pds (some alice)
#guard sends s4.2 == [(2, .refresh, pds ++ "/xrpc/com.atproto.server.refreshSession", some "refresh")]
def s5 := step s4.1 (.call 8 .getSession)
#guard s5.2.isEmpty && s5.1.held.length == 2
#guard (step s5.1 (.reply 99 ok)).1 == s5.1
-- The refresh succeeds: both calls are sent, the first for the second time.
def s6 := step s5.1 (.reply 2 okSession)
#guard s6.1.phase == .signedIn alice && s6.1.held.isEmpty
#guard sends s6.2 == [(3, .call 0, pds ++ "/xrpc/app.bsky.feed.getTimeline?limit=50", some "access"),
                      (4, .call 1, pds ++ "/xrpc/com.atproto.server.getSession", some "access")]
#guard s6.1.inflight.map (fun (r, p) => (r, p.tries)) == [(3, 2), (4, 1)]
-- Expired again on its second try: answered, no new refresh.
def s7 := step s6.1 (.reply 3 expired)
#guard sends s7.2 == [] && answers s7.2 == [(7, true)]
-- A duplicate reply is ignored.
#guard (step s7.1 (.reply 3 ok)).2.isEmpty

-- A refused refresh: both items forgotten, the held calls answered, signed out.
def r1 := step s3.1 (.reply 1 expired)
def r2 := step r1.1 (.call 9 .getSession)
def r3 := step r2.1 (.reply 2 invalid)
#guard r3.1.phase == .signedOut && r3.1.held.isEmpty
#guard forgets r3.2 == ["access", "refresh"] && answers r3.2 == [(7, false), (9, false)]
-- Signed out: a call is answered at once and nothing is sent.
def r4 := step r3.1 (.call 10 .getSession)
#guard sends r4.2 == [] && answers r4.2 == [(10, false)]

-- A refresh that got no answer: the held call fails with it, the session stays.
def t1 := step r1.1 (.reply 2 (.failed .network "offline"))
#guard t1.1.phase == .signedIn alice && forgets t1.2 == [] && answers t1.2 == [(7, true)]

-- Resume at launch: a refresh with the saved host; a missing item signs out.
def l1 := step init (.resume host)
#guard sends l1.2 == [(0, .refresh, host ++ "/xrpc/com.atproto.server.refreshSession", some "refresh")]
#guard (step l1.1 (.reply 0 okSession)).1.phase == .signedIn alice
#guard (step l1.1 (.reply 0 (.failed .notFound "no item"))).1.phase == .signedOut
#guard (step l1.1 (.reply 0 (.failed .timeout "slow"))).1.phase == .launched
-- A call made while resuming waits for it.
def l2 := step l1.1 (.call 3 .getSession)
#guard l2.2.isEmpty && sends (step l2.1 (.reply 0 okSession)).2 ==
  [(1, .call 0, pds ++ "/xrpc/com.atproto.server.getSession", some "access")]

-- Sign out while signing in: the sign-in is abandoned; until its reply, signIn is busy; its
-- reply (which may have stored tokens) makes the session forget both items again.
def a1 := step s1.1 .signOut
#guard a1.1.phase == .signedOut && a1.1.abandoned == [0] && forgets a1.2 == ["access", "refresh"]
#guard (step a1.1 (.signIn host "alice.test" "pw")).2 == [.event .busy]
def a2 := step a1.1 (.reply 0 okSession)
#guard a2.1.phase == .signedOut && a2.1.abandoned.isEmpty && forgets a2.2 == ["access", "refresh"]
#guard ((step a2.1 (.signIn host "alice.test" "pw")).1.phase matches .signingIn ..)

-- Cancel: a call in flight has its request cancelled and is never answered; a held one is
-- dropped and not sent after the refresh; other calls are untouched.
def c1 := step s2.1 (.call 7 (.getTimeline (some 50) none))
def c2 := step c1.1 (.call 8 .getSession)
def c3 := step c2.1 (.cancel [7])
#guard cancels c3.2 == [1] && answers c3.2 == [] && c3.1.inflight.map (·.1) == [2]
#guard (step c3.1 (.reply 1 ok)).2.isEmpty
#guard (step c3.1 (.cancel [99])).2.isEmpty && (step c3.1 (.cancel [99])).1 == c3.1
def h1 := step s4.1 (.call 8 .getSession)
def h2 := step h1.1 (.cancel [8])
#guard h2.2.isEmpty && h2.1.held.map (·.id) == [7]
#guard sends (step h2.1 (.reply 2 okSession)).2 ==
  [(3, .call 0, pds ++ "/xrpc/app.bsky.feed.getTimeline?limit=50", some "access")]
