import CairnAtproto

open CairnJson CairnAtproto CairnAtproto.Fake CairnAtproto.Session

/-! The fake PDS: dates, the timeline and its cursors, sessions and the host, and the
`cairn fuzz` hook. -/

namespace FakeTests

def cfg : Config := { seed := 7, base := 10, arrival := 0, life := 2 }

-- Dates as JavaScript's `toISOString` writes them; `parseDatetime` reads them back.
#guard iso 0 == "1970-01-01T00:00:00.000Z"
#guard iso 951782400000 == "2000-02-29T00:00:00.000Z"
#guard iso epoch == "2026-10-01T00:00:00.000Z"
#guard iso 4107542399999 == "2100-02-28T23:59:59.999Z"
#guard (List.range 50).all fun k => parseDatetime (iso (createdMs cfg k)) == some (createdMs cfg k)
-- Posts are in time order.
#guard (List.range 50).all fun k => createdMs cfg k < createdMs cfg (k + 1)

-- Every post decodes and round-trips.
#guard (List.range 30).all fun k => FeedItem.ofJson (postAt cfg k).toJson == some (postAt cfg k)
#guard (decode (encode (page cfg 30 30 none).toJson)).bind FeedPage.ofJson == some (page cfg 30 30 none)

-- Paging: newest first, contiguous, the cursor names the oldest post of the page.
#guard (page cfg 10 3 none).feed.map (·.post.uri) == [9, 8, 7].map (postUri cfg)
#guard (page cfg 10 3 none).cursor == some (cursorOf cfg 7)
#guard cursorPos cfg 10 (cursorOf cfg 7) == some 7
#guard (page cfg 10 3 (some 7)).feed.map (·.post.uri) == [6, 5, 4].map (postUri cfg)
#guard (page cfg 10 50 (some 2)).feed.length == 2 && (page cfg 10 50 (some 2)).cursor == none
-- Walking the cursors from the head visits the whole timeline once, in order.
def walk (length limit : Nat) : Nat → Option Nat → List FeedItem
  | 0, _ => []
  | n + 1, before =>
    let p := page cfg length limit before
    p.feed ++ match p.cursor with
      | some c => walk length limit n (cursorPos cfg length c)
      | none => []
#guard walk 10 3 10 none == timeline cfg 10
#guard walk 23 4 10 none == timeline cfg 23
-- A cursor stays valid as posts arrive at the head, and means the same posts.
#guard cursorPos cfg 50 (cursorOf cfg 7) == some 7
#guard (timeline cfg 12).drop 2 == timeline cfg 10
-- Not a cursor: garbage, post 0, a post not there yet, another seed's.
#guard cursorPos cfg 10 "garbage" == none
#guard cursorPos cfg 10 (cursorOf cfg 0) == none
#guard cursorPos cfg 10 (cursorOf cfg 12) == none
#guard cursorPos cfg 10 (cursorOf { cfg with seed := 8 } 7) == none

-- Query strings are read as `URLSearchParams` reads them.
#guard splitPath "/xrpc/x?limit=3&cursor=a%3A%3Ab+c&&flag" ==
  ("/xrpc/x", [("limit", "3"), ("cursor", "a::b c"), ("flag", "")])
#guard formDecode "%E6%97%A5%zz%" == "日%zz%"

-- The server: sign in, page, expire after `life` calls, refresh, rotation.
def s0 := Server.init cfg
def signIn (pw : String) : Req :=
  { method := "POST", path := "/xrpc/" ++ nsidCreateSession,
    body := encode (.obj [("identifier", .str cfg.identifier), ("password", .str pw)]) }
def status : Response → Nat
  | .json st .. => st
  | _ => 0
def errName : Response → String
  | .json _ _ b _ => (b.str? "error").getD ""
  | _ => ""
#guard status (s0.handle (signIn "nope")).2 == 401
def s1 := (s0.handle (signIn cfg.password)).1
#guard s1.live.map (·.gen) == some 1
def tl (gen : Nat) (q : String := "") : Req :=
  { method := "GET", path := "/xrpc/" ++ nsidGetTimeline ++ q,
    authorization := some ("Bearer " ++ token cfg "access" gen) }
def refresh (gen : Nat) : Req :=
  { method := "POST", path := "/xrpc/" ++ nsidRefreshSession,
    authorization := some ("Bearer " ++ token cfg "refresh" gen) }
-- The first token serves `lifeOf 1` calls, then `ExpiredToken`.
def uses (s : Server) (gen : Nat) : Nat → Server × List Nat
  | 0 => (s, [])
  | n + 1 => let (s, r) := s.handle (tl gen); let (s, rs) := uses s gen n; (s, status r :: rs)
#guard (uses s1 1 (cfg.lifeOf 1 + 1)).2 == List.replicate (cfg.lifeOf 1) 200 ++ [400]
#guard errName (((uses s1 1 (cfg.lifeOf 1)).1).handle (tl 1)).2 == "ExpiredToken"
def s2 := (s1.handle (refresh 1)).1
#guard s2.live.map (·.gen) == some 2
#guard errName (s2.handle (refresh 1)).2 == "InvalidToken"
#guard errName (s2.handle (tl 1)).2 == "ExpiredToken"
#guard status (s2.handle (tl 2)).2 == 200
#guard errName ((s2.control .expire).handle (tl 2)).2 == "ExpiredToken"
#guard errName ((s2.control .revoke).handle (refresh 2)).2 == "InvalidToken"
#guard status (s2.handle { tl 2 with authorization := none }).2 == 401
-- Faults come in order, then the method answers again.
def s3 := s2.control (.fail 2 .rateLimit)
#guard status (s3.handle (tl 2)).2 == 429
#guard match ((s3.handle (tl 2)).1.handle (tl 2)).2 with | .json 429 hs _ _ => ratelimitReset hs |>.isSome | _ => false
#guard status ((((s3.handle (tl 2)).1.handle (tl 2)).1).handle (tl 2)).2 == 200
#guard match ((s2.control (.fail 1 .timeout)).handle (tl 2)).2 with | .hang => true | _ => false
-- Posts arrive at the head; an image is its size.
#guard ((s2.control (.post 5)).handle (tl 2 "?limit=1")).1.length == 15
#guard match (s0.handle { method := "GET", path := "/img/30x20/a.png" }).2 with | .png 30 20 => true | _ => false

-- The host: capture blanks the tokens and keeps them in the Keychain; the session runs on it.
def w0 := World.init cfg
/-- The host answers every request at once, in order, and the requests those answers make. -/
def serve : Nat → World → State → List Out → World × State × List Out
  | 0, w, s, _ => (w, s, [])
  | _, w, s, [] => (w, s, [])
  | n + 1, w, s, o :: os =>
    match o with
    | .send rid _ h =>
      let (w, r) := w.send h
      let (s, o2) := step s (.reply rid r)
      let (w, s, rest) := serve n w s (os ++ o2)
      (w, s, o2 ++ rest)
    | .forget _ item => serve n (w.forget item) s os
    | _ => serve n w s os
def run (w : World) (s : State) : List Input → World × State × List Out
  | [] => (w, s, [])
  | i :: is =>
    let (s, outs) := step s i
    let (w, s, more) := serve 1000 w s outs
    let (w, s, rest) := run w s is
    (w, s, outs ++ more ++ rest)
def r1 := run w0 init [.signIn cfg.service cfg.identifier cfg.password, .call 0 (.getTimeline (some 3))]
#guard r1.1.generation accessItem == some 1 && r1.1.generation refreshItem == some 1
#guard match r1.2.1.phase with | .signedIn a => a.handle == cfg.identifier && a.service == cfg.service | _ => false
#guard !(hasMarker (reprStr r1.2.1)) && !(r1.2.2.any fun o => hasMarker (reprStr o))
-- More calls than the token serves: the session refreshes, the host captures the new pair.
def r2 := run r1.1 r1.2.1 ((List.range 6).map fun i => .call (i + 1) (.getTimeline (some 1)))
#guard (r2.1.generation accessItem).getD 0 > 1
#guard r2.2.2.all fun o => match o with | .answer _ (.reply (.http st ..)) => st == 200 | _ => true
-- Signing out forgets both items; a resume then fails with no item and signs out.
def r3 := run r2.1 r2.2.1 [.signOut]
#guard r3.1.items.isEmpty
-- With capture off, the tokens reach Lean: what fake-fuzz's control run relies on.
def r4 := run { w0 with captures := false } init [.signIn cfg.service cfg.identifier cfg.password]
#guard (w0.send (createSession cfg.service cfg.identifier cfg.password)).2 |> replyHasMarker |> not
#guard ({ w0 with captures := false }.send (createSession cfg.service cfg.identifier cfg.password)).2 |> replyHasMarker

-- The `cairn fuzz` hook has `Custom.replies`'s type, and answers timeline URLs with pages.
def custom : Cairn.Fuzz.Custom State :=
  { replies := replies cfg { phase := fun s => some s.phase } }
def tlReq : Cairn.Request := Call.http (.getTimeline (some 2)) cfg.service
def hookReplies : List Cairn.Reply :=
  (List.range 40).filterMap fun i =>
    ((replies cfg ({} : Hooks Unit)) () 5 tlReq).map fun g => (g.run' (Cairn.Fuzz.Rng.ofSeed i))
#guard hookReplies.length == 40
#guard hookReplies.any fun | .http 200 _ b => ((decodeBytes b).bind FeedPage.ofJson).isSome | _ => false
#guard hookReplies.any fun r => isExpired r
#guard hookReplies.all fun r => match r with
  | .http 200 _ b => ((decodeBytes b).bind FeedPage.ofJson).map (·.feed.length) == some 2
  | _ => true
-- A session reply through the hook carries no marker (it captures what the request asks); without
-- capture it would, and so would a createSession that asked for none.
def csReq : Cairn.Request := createSession cfg.service cfg.identifier cfg.password
def csBare : Cairn.Request :=
  .http "POST" (cfg.service ++ "/xrpc/" ++ nsidCreateSession) []
    (encode (.obj [("identifier", .str cfg.identifier), ("password", .str cfg.password)])).toUTF8 30000
#guard (List.range 40).all fun i =>
  (((replies cfg ({} : Hooks Unit)) () 0 csReq).map fun g => !(replyHasMarker (g.run' (Cairn.Fuzz.Rng.ofSeed i)))) == some true
#guard (List.range 40).any fun i =>
  (((replies cfg ({ capture := fun _ _ _ => [] } : Hooks Unit)) () 0 csReq).map fun g =>
    replyHasMarker (g.run' (Cairn.Fuzz.Rng.ofSeed i))) == some true
#guard (List.range 40).any fun i =>
  (((replies cfg ({} : Hooks Unit)) () 0 csBare).map fun g =>
    replyHasMarker (g.run' (Cairn.Fuzz.Rng.ofSeed i))) == some true
-- A request with no secret gets no token: the timeline answers 401.
#guard (List.range 40).all fun i =>
  (((replies cfg ({} : Hooks Unit)) () 5 (query cfg.service nsidGetTimeline)).map fun g =>
    match g.run' (Cairn.Fuzz.Rng.ofSeed i) with
    | .http st .. => st != 200 | _ => true) == some true
#guard match ((replies cfg ({} : Hooks Unit)) () 0 (.loadImage (cfg.service ++ "/img/40x30/x.png") false)).map
  (fun g => g.run' (Cairn.Fuzz.Rng.ofSeed 0)) with | some (Cairn.Reply.image 40 30) => true | _ => false

-- Replies (cairn#236): some posts reply to an older post, a deleted one or a blocked one; the
-- record's reply names the same parent the view does, and a reply's parent is older.
def kinds (k : Nat) : String :=
  match (postAt cfg k).reply with
  | some r => match r.parent with
    | .post _ => "post" | .notFound _ => "notFound" | .blocked _ => "blocked" | .other _ => "other"
  | none => "none"
#guard ["none", "post", "notFound", "blocked"].all fun x => (List.range 200).any (kinds · == x)
#guard (List.range 200).all fun k => (postAt cfg k).reply.isSome == (postAt cfg k).post.reply.isSome
#guard (List.range 200).all fun k => match replyTarget cfg k with
  | some (.post j) => j < k && (postAt cfg k).post.reply.map (·.parent.uri) == some (postUri cfg j)
  | _ => true
#guard (List.range 100).all fun k => FeedItem.ofJson (postAt cfg k).toJson == some (postAt cfg k)

end FakeTests
