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

/-! ### The tester's repo, other accounts, the AppView's lag, notifications (cairn#251) -/

-- A long-lived session, no other accounts acting on their own, no lag (changed below).
def ac : Config := { seed := 11, base := 40, arrival := 0, life := 2, act := 0, lag := 0 }
def a0 : Server := { Server.init ac with issued := 1, live := some { gen := 1, life := 1000000 } }
def bearer : Option String := some ("Bearer " ++ token ac "access" 1)
def get (nsid : String) (q : String := "") : Req :=
  { method := "GET", path := "/xrpc/" ++ nsid ++ q, authorization := bearer }
def post (nsid : String) (body : Json) : Req :=
  { method := "POST", path := "/xrpc/" ++ nsid, authorization := bearer, body := encode body }
def bodyOf : Response → Json
  | .json _ _ b _ => b
  | _ => .null
/-- Requests in order: the server after, and the replies. -/
def sends (s : Server) : List Req → Server × List Response
  | [] => (s, [])
  | r :: rs => let (s, x) := s.handle r; let (s, xs) := sends s rs; (s, x :: xs)

def k5 : Nat := 5
def ref5 : StrongRef := { uri := postUri ac k5, cid := postCid ac k5 }
def like5 : PutRecord := { repo := ac.did, rkey := "3l2aaaaaaaa2a", record := .like ref5 "2026-10-02T00:00:00.000Z" }
def putLike := post nsidPutRecord like5.toJson
def getLike := get nsidGetRecord ("?" ++ "&".intercalate ((getRecordParams like5.uri).map fun (k, v) => k ++ "=" ++ v))
def getPost5 := get nsidGetPosts ("?uris=" ++ postUri ac k5)
def likes5 (r : Response) : Option (Nat × Bool) :=
  ((Posts.ofJson (bodyOf r)).bind (·.posts.head?)).map fun p => (p.likeCount, p.viewer.like.isSome)

-- putRecord: 200, getRecord reads it back, the post shows the like and the viewer's like.
def b1 := sends a0 [putLike, getLike, getPost5]
#guard b1.2.map status == [200, 200, 200]
#guard (RecordView.ofJson (bodyOf (b1.2.getD 1 .hang))).map (·.value) == some like5.record
#guard likes5 (b1.2.getD 2 .hang) == some (seededLikes ac k5 + 1, true)
-- Sent again: the same record, so nothing changes.
#guard (b1.1.putRec like5).1.log.length == b1.1.log.length
#guard (sends b1.1 [putLike]).1.now.repo == b1.1.now.repo
-- deleteRecord: gone from getRecord at once, and from the post; twice is fine.
def b2 := sends b1.1 [post nsidDeleteRecord (deleteRecordJson like5.uri), getLike, getPost5,
  post nsidDeleteRecord (deleteRecordJson like5.uri)]
#guard b2.2.map status == [200, 400, 200, 200]
#guard errName (b2.2.getD 1 .hang) == "RecordNotFound"
#guard likes5 (b2.2.getD 2 .hang) == some (seededLikes ac k5, false)
-- Refused writes: another account's repo, a bad key, a record of another collection, a bad body.
#guard (sends a0 [post nsidPutRecord { like5 with repo := "did:plc:fakeauthorada" }.toJson,
  post nsidPutRecord { like5 with rkey := "a/b" }.toJson,
  post nsidPutRecord { like5 with record := .other "app.bsky.feed.post" }.toJson,
  post nsidPutRecord (.obj [("repo", .str ac.did)])]).2.map status == [400, 400, 400, 400]

-- The AppView lags: with lag 5 the like shows up on the post only later; getRecord at once.
def l0 : Server := { a0 with lag := 5 }
def l1 := sends l0 [putLike, getLike]
#guard status (l1.2.getD 1 .hang) == 200
#guard (List.range 8).any fun n => likes5 ((sends l1.1 (List.replicate n getPost5)).2.getLast?.getD .hang) == some (seededLikes ac k5, false)
#guard likes5 ((l1.1.control .catchup).handle getPost5).2 == some (seededLikes ac k5 + 1, true)
#guard likes5 ((sends l1.1 (List.replicate 7 getPost5)).2.getLast?.getD .hang) == some (seededLikes ac k5 + 1, true)

-- Mutes: the muted account's posts leave the timeline; muting oneself or nobody is refused.
def authorOf5 : String := (poster ac k5).did
#guard !isMine ac k5
def m1 := sends a0 [post nsidMuteActor (.obj [("actor", .str authorOf5)]), get nsidGetTimeline "?limit=100"]
#guard m1.1.now.muted == [authorOf5]
#guard ((FeedPage.ofJson (bodyOf (m1.2.getD 1 .hang))).map fun p => p.feed.all (·.post.author.did != authorOf5)) == some true
#guard (sends a0 [get nsidGetTimeline "?limit=100"]).2.head?.bind (fun r => (FeedPage.ofJson (bodyOf r)).map
  fun p => p.feed.any (·.post.author.did == authorOf5)) == some true
#guard errName (a0.handle (post nsidMuteActor (.obj [("actor", .str ac.did)]))).2 == "InvalidRequest"
#guard errName (a0.handle (post nsidMuteActor (.obj [("actor", .str "nobody.test")]))).2 == "InvalidRequest"
#guard (sends m1.1 [post nsidUnmuteActor (.obj [("actor", .str authorOf5)])]).1.now.muted == []
-- getProfile: the tester and others, with the viewer's mute.
#guard ((ProfileDetail.ofJson (bodyOf (m1.1.handle (get nsidGetProfile ("?actor=" ++ authorOf5))).2)).map
  (·.profile.viewer.muted)) == some true

-- Other accounts act: a like of the tester's newest post counts and notifies.
def mine : Nat := (a0.newestMine).getD 0
#guard isMine ac mine
def o1 := (a0.control (.act .like 2 none)).handle (get nsidGetPosts ("?uris=" ++ postUri ac mine))
#guard likes5 o1.2 == some (seededLikes ac mine + 1, false)
def n1 := (sends (a0.control (.act .like 2 none)) [get nsidListNotifications "?limit=100"]).2.head?.getD .hang
#guard ((NotificationPage.ofJson (bodyOf n1)).map fun p => p.notifications.any (·.reason == .like)) == some true
-- Again: the like is taken back.
#guard likes5 (((a0.control (.act .like 2 none)).control (.act .like 2 none)).handle
  (get nsidGetPosts ("?uris=" ++ postUri ac mine))).2 == some (seededLikes ac mine, false)

-- Notifications: newest first, paged by cursor without gaps; updateSeen marks them read.
def nAll := ((NotificationPage.ofJson (bodyOf (a0.handle (get nsidListNotifications "?limit=100")).2)).map
  (·.notifications)).getD []
#guard nAll.length ≥ 3
def nWalk : Nat → Server → Option String → List Notification
  | 0, _, _ => []
  | n + 1, s, cur =>
    let (s, r) := s.handle (get nsidListNotifications ("?limit=2" ++ (cur.map ("&cursor=" ++ ·)).getD ""))
    match NotificationPage.ofJson (bodyOf r) with
    | some p => p.notifications ++ (match p.cursor with | some c => nWalk n s (some c) | none => [])
    | none => []
#guard (nWalk 50 a0 none).map (·.uri) == nAll.map (·.uri)
#guard nAll.all (!·.isRead)
def seen1 := sends a0 [post nsidUpdateSeen (seenAtJson "2030-01-01T00:00:00.000Z"), get nsidGetUnreadCount]
#guard (seen1.2.getLast?.map bodyOf).bind unreadCountOf == some 0
#guard ((a0.handle (get nsidGetUnreadCount)).2 |> bodyOf |> unreadCountOf) == some nAll.length
#guard errName (a0.handle (post nsidUpdateSeen (seenAtJson "yesterday"))).2 == "InvalidRequest"

-- Write faults: 400 before (not applied), lost after (applied, no reply).
#guard match ((a0.control (.fail 1 .refused)).handle putLike) with
  | (s, r) => status r == 400 && s.now.repo.isEmpty
#guard match ((a0.control (.fail 1 .lostAfter)).handle putLike) with
  | (s, .hang) => s.now.repo.length == 1
  | _ => false
-- An expired token: refused and not applied.
#guard match ((a0.control .expire).handle putLike) with
  | (s, r) => errName r == "ExpiredToken" && s.now.repo.isEmpty

-- The world's accessors, for `cairn fuzz` checks.
def wl : World := { World.init ac with server := b1.1 }
#guard wl.likedBy (postUri ac k5) && !wl.repostedBy (postUri ac k5)
#guard wl.likeCount (postUri ac k5) == seededLikes ac k5 + 1
#guard !wl.muted authorOf5 && ({ wl with server := m1.1 } : World).muted authorOf5
#guard wl.seenAt == none && ({ wl with server := seen1.1 } : World).seenAt.isSome
#guard handles (Call.http (.getTimeline none) ac.service) && !handles (.loadImage (ac.service ++ "/img/1x1/a.png") false)

end FakeTests
