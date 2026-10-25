module

public import CairnAtproto.Lexicon.Server
public import CairnAtproto.Lexicon.Feed

/-! # The session machine

`CairnAtproto.Session` turns an app's XRPC calls into requests that carry its session, and
keeps the session alive. It is a pure state machine: `step` takes one `Input` (something the
app asked for, or a reply from the host) and gives the new `State` and a list of `Out`s (requests
to send, items to forget, answers and events for the app). The app routes replies back by the
request ids the session chose.

    launched ──resume──▶ refreshing ──ok──▶ signed in ◀──ok── refreshing ◀─ExpiredToken─┐
       │                     │ refused/                │                                   │
     signIn               transient                    └───────────────────────────────────┘
       ▼                     ▼
    signing in ──ok──▶ signed in            any phase ──signOut──▶ signed out ──signIn──▶ …

* **Tokens never reach Lean.** `createSession` and `refreshSession` capture `accessJwt` and
  `refreshJwt` into the Keychain items `access` and `refresh` (cairn#205); calls carry
  `Authorization: Bearer <access>`, named by item. The state holds DIDs, handles, service URLs,
  request ids and the app's calls; `SessionInfo` has no token field.
* **The password** is in the one `createSession` request, marked `redact`; no state holds it.
* **One refresh at a time.** A call answered `ExpiredToken` the first time it was sent starts a
  `refreshSession` (authorised by `refresh`), or joins the one in flight, and is held. Calls the
  app makes meanwhile are held too. When the refresh succeeds every held call is sent (again),
  so a call is sent at most twice, the second time only after a successful refresh.
* **A refused refresh signs out**: it forgets both items and answers every held call
  `signedOut`. A refresh that never got an answer (network, timeout, 5xx, 429) doesn't: the
  held calls are answered with its failure and the session stays as it was.
* **No session, no secret.** Signed out or signing in, a call is answered `signedOut` at once
  and nothing carrying a Keychain secret is sent.
* **Sign out** forgets both items and answers the held calls. A sign-in or refresh still in flight
  is abandoned: its reply, which may have written new tokens, makes the session forget both
  items again, and until it arrives `signIn` answers `busy`.

The claims about it (`cairn_atproto^N`) are in `CairnAtproto.Claims`, with proofs in
`CairnAtproto.Proofs.Session`. -/

@[expose] public section

namespace CairnAtproto.Session
open CairnJson CairnAtproto

/-- The signed-in account: Lean holds its DID, handle and service URL, never its tokens. -/
structure Account where
  did : String
  handle : String
  /-- Where calls go: the PDS from the DID document, else the host signed in to. -/
  service : String
deriving Repr, DecidableEq, Inhabited

/-- An XRPC call the app wants made with the session. -/
structure Call where
  nsid : String
  /-- A procedure (POST with `body`); otherwise a query (GET with `params`). -/
  procedure : Bool := false
  params : List (String × String) := []
  /-- JSON text, for a procedure. -/
  body : String := ""
deriving Repr, DecidableEq, Inhabited

/-- The request for a call, authorised by the access token. -/
def Call.http (c : Call) (service : String) : Http :=
  if c.procedure then
    { method := .post, url := xrpcUrl service c.nsid c.params,
      headers := [("Accept", "application/json"), ("Content-Type", "application/json")],
      body := c.body, secret := some { account := accessItem } }
  else query service c.nsid c.params (secret := some { account := accessItem })

/-- `getTimeline`: the home feed, `limit` posts (1 to 100; the server's default is 50) after
`cursor`. -/
def Call.getTimeline (limit : Option Nat := none) (cursor : Option String := none) : Call :=
  { nsid := nsidGetTimeline, params := pageParams limit cursor }

/-- `getAuthorFeed` for `actor` (a handle or DID). -/
def Call.getAuthorFeed (actor : String) (limit : Option Nat := none)
    (cursor : Option String := none) : Call :=
  { nsid := nsidGetAuthorFeed, params := ("actor", actor) :: pageParams limit cursor }

/-- `getSession`: who the session is. -/
def Call.getSession : Call := { nsid := nsidGetSession }

inductive Phase where
  /-- At launch, before `resume` or `signIn`: there may be items from an earlier run. -/
  | launched
  /-- No session, and the items are forgotten (or were never there). -/
  | signedOut
  /-- `createSession` request `rid` to `host` is in flight. -/
  | signingIn (rid : Nat) (host : String)
  | signedIn (a : Account)
  /-- `refreshSession` request `rid` to `host` is in flight; `a` is the account it refreshes,
  `none` when resuming at launch. -/
  | refreshing (rid : Nat) (host : String) (a : Option Account)
deriving Repr, DecidableEq, Inhabited

/-- A call the session has taken on: the app's id for it, the session's ticket (unique), and how
many times it has been sent. -/
structure Pending where
  id : Nat
  ticket : Nat
  call : Call
  tries : Nat
deriving Repr, DecidableEq, Inhabited

structure State where
  phase : Phase := .launched
  /-- The next request id. Request ids are the session's: the app sends each request under
  its id (so it keeps its own requests' ids apart) and hands its reply back with it. -/
  next : Nat := 0
  /-- The next call ticket. -/
  nextTicket : Nat := 0
  /-- Calls sent and not answered, by request id. -/
  inflight : List (Nat × Pending) := []
  /-- Calls waiting for the refresh in flight, oldest first. -/
  held : List Pending := []
  /-- Sign-in and refresh requests in flight that sign-out abandoned. -/
  abandoned : List Nat := []
deriving Repr, DecidableEq, Inhabited

/-- What a request is for. -/
inductive Kind where
  | signIn
  | refresh
  /-- Ticket `t`'s call. -/
  | call (t : Nat)
deriving Repr, DecidableEq, Inhabited

/-- How a call ended, for the app. -/
inductive Answer where
  /-- The reply to its last send, whatever it says (`Outcome.ofReply` reads it); or, for a call
  held for a refresh that never got an answer, that refresh's failure. -/
  | reply (r : Cairn.Reply)
  /-- Not sent, or not sent again: there is no session, or its refresh was refused. -/
  | signedOut
deriving Repr, BEq, Inhabited

/-- Why the session ended. -/
inductive Why where
  | requested
  /-- The server refused the refresh (or the items were gone). -/
  | refused
deriving Repr, DecidableEq, Inhabited

inductive Event where
  /-- Signed in, or resumed at launch. -/
  | signedIn (a : Account)
  /-- The tokens were refreshed; the account may have a new handle or PDS. -/
  | refreshed (a : Account)
  /-- `createSession` failed: its reply (an error, or a body that isn't a session). -/
  | signInFailed (r : Cairn.Reply)
  /-- A refresh got no answer (network, timeout, 5xx, 429); nothing changed. -/
  | refreshFailed (r : Cairn.Reply)
  | signedOut (why : Why)
  /-- `signIn` came while a session is live or being made, or while an abandoned one's reply
  is outstanding; it did nothing. -/
  | busy
deriving Repr, BEq, Inhabited

inductive Out where
  /-- Send request `rid`. -/
  | send (rid : Nat) (kind : Kind) (h : Http)
  /-- Delete the Keychain item (cairn#205's `Request.forgetSecret`) as request `rid`. -/
  | forget (rid : Nat) (item : String)
  /-- The app's call `id` has ended. -/
  | answer (id : Nat) (a : Answer)
  | event (e : Event)
deriving Repr, BEq, Inhabited

inductive Input where
  /-- Sign in at `host` with a handle or email and an app password. -/
  | signIn (host identifier password : String)
  /-- At launch: resume the session the items hold, with `host` (the service the app saved). -/
  | resume (host : String)
  /-- Make call `c`; the app's id `id` comes back in its `answer`. -/
  | call (id : Nat) (c : Call)
  | signOut
  /-- The host's reply to request `rid`. -/
  | reply (rid : Nat) (r : Cairn.Reply)
deriving Repr, BEq, Inhabited

def init : State := {}

/-! ## Reading replies -/

/-- The account a session reply describes: a 2xx with a session body. -/
def sessionOf : Cairn.Reply → Option SessionInfo
  | .http st _ body => if isSuccess st then (decodeBytes body).bind SessionInfo.ofJson else none
  | _ => none

/-- A refresh that got no answer, rather than a refusal: the network, a timeout, 5xx, 429. -/
def transient : Cairn.Reply → Bool
  | .http st _ _ => 500 ≤ st || st == 429
  | .failed f _ => f == .timeout || f == .network || f == .other
  | _ => false

def isExpired (r : Cairn.Reply) : Bool := errorOf r == some .expiredToken

def Account.ofInfo (i : SessionInfo) (host : String) : Account :=
  { did := i.did, handle := i.handle, service := i.pds.getD host }

/-! ## Steps -/

/-- Send `p` (once more) to `service`. -/
def sendCall (service : String) (s : State) (p : Pending) : State × List Out :=
  ({ s with next := s.next + 1, inflight := (s.next, { p with tries := p.tries + 1 }) :: s.inflight },
   [.send s.next (.call p.ticket) (p.call.http service)])

/-- Each with its request id, from `n` up. -/
def numbered (n : Nat) : List Pending → List (Nat × Pending)
  | [] => []
  | p :: ps => (n, p) :: numbered (n + 1) ps

/-- Send each, oldest first, to `service`, once more. -/
def sendAll (service : String) (s : State) (ps : List Pending) : State × List Out :=
  let ns := numbered s.next ps
  ({ s with next := s.next + ps.length,
            inflight := ns.map (fun x => (x.1, { x.2 with tries := x.2.tries + 1 })) ++ s.inflight },
   ns.map fun x => .send x.1 (.call x.2.ticket) (x.2.call.http service))

/-- Forget both items. -/
def forgetBoth (s : State) : State × List Out :=
  ({ s with next := s.next + 2 }, [.forget s.next accessItem, .forget (s.next + 1) refreshItem])

def answerAll (ps : List Pending) (a : Answer) : List Out := ps.map fun p => .answer p.id a

/-- Start a refresh of `a`, holding `p`. -/
def startRefresh (s : State) (a : Account) (p : Pending) : State × List Out :=
  ({ s with phase := .refreshing s.next a.service (some a), next := s.next + 1,
            held := s.held ++ [p] },
   [.send s.next .refresh (refreshSession a.service)])

/-- The reply to a call in flight (or to anything else the session doesn't wait for). -/
def onCallReply (s : State) (rid : Nat) (r : Cairn.Reply) : State × List Out :=
  if rid ∈ s.abandoned then
    let (s₁, o) := forgetBoth { s with abandoned := s.abandoned.filter (· ≠ rid) }
    (s₁, o)
  else
    match s.inflight.find? (·.1 == rid) with
    | none => (s, [])
    | some (_, p) =>
      let s := { s with inflight := s.inflight.filter (·.1 ≠ rid) }
      if isExpired r && p.tries == 1 then
        match s.phase with
        | .signedIn a => startRefresh s a p
        | .refreshing .. => ({ s with held := s.held ++ [p] }, [])
        | _ => (s, [.answer p.id (.reply r)])
      else (s, [.answer p.id (.reply r)])

/-- The reply to the sign-in in flight. -/
def onSignIn (s : State) (host : String) (r : Cairn.Reply) : State × List Out :=
  match sessionOf r with
  | some i =>
    let a := Account.ofInfo i host
    ({ s with phase := .signedIn a }, [.event (.signedIn a)])
  | none =>
    let (s₁, o) := forgetBoth { s with phase := .signedOut }
    (s₁, o ++ [.event (.signInFailed r)])

/-- The reply to the refresh in flight. -/
def onRefresh (s : State) (host : String) (prev : Option Account) (r : Cairn.Reply) :
    State × List Out :=
  match sessionOf r with
  | some i =>
    let a := Account.ofInfo i host
    let ev : Event := if prev.isSome then .refreshed a else .signedIn a
    let (s₁, o) := sendAll a.service { s with phase := .signedIn a, held := [] } s.held
    (s₁, .event ev :: o)
  | none =>
    if transient r then
      let phase := match prev with | some a => Phase.signedIn a | none => .launched
      ({ s with phase, held := [] }, answerAll s.held (.reply r) ++ [.event (.refreshFailed r)])
    else
      let (s₁, o) := forgetBoth { s with phase := .signedOut, held := [] }
      (s₁, answerAll s.held .signedOut ++ o ++ [.event (.signedOut .refused)])

def step (s : State) : Input → State × List Out
  | .signIn host identifier password =>
    match s.phase with
    | .launched | .signedOut =>
      if s.abandoned.isEmpty then
        ({ s with phase := .signingIn s.next host, next := s.next + 1 },
         [.send s.next .signIn (createSession host identifier password)])
      else (s, [.event .busy])
    | _ => (s, [.event .busy])
  | .resume host =>
    match s.phase with
    | .launched =>
      ({ s with phase := .refreshing s.next host none, next := s.next + 1 },
       [.send s.next .refresh (refreshSession host)])
    | _ => (s, [])
  | .call id c =>
    let p : Pending := { id, ticket := s.nextTicket, call := c, tries := 0 }
    let s' := { s with nextTicket := s.nextTicket + 1 }
    match s.phase with
    | .signedIn a => sendCall a.service s' p
    | .refreshing .. => ({ s' with held := s.held ++ [p] }, [])
    | _ => (s', [.answer id .signedOut])
  | .signOut =>
    let ab := match s.phase with
      | .signingIn rid _ => [rid]
      | .refreshing rid _ _ => [rid]
      | _ => []
    let (s₁, o) := forgetBoth { s with phase := .signedOut, held := [],
                                       abandoned := ab ++ s.abandoned }
    (s₁, answerAll s.held .signedOut ++ o ++ [.event (.signedOut .requested)])
  | .reply rid r =>
    match s.phase with
    | .signingIn rid' host => if rid = rid' then onSignIn s host r else onCallReply s rid r
    | .refreshing rid' host a => if rid = rid' then onRefresh s host a r else onCallReply s rid r
    | _ => onCallReply s rid r

/-- The state after a run of inputs, and everything it put out. -/
def run (s : State) : List Input → State × List Out
  | [] => (s, [])
  | i :: is =>
    let (s₁, o₁) := step s i
    let (s₂, o₂) := run s₁ is
    (s₂, o₁ ++ o₂)

end CairnAtproto.Session
