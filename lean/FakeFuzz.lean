import CairnAtproto

/-! `lake exe fake-fuzz [--sequences N] [--steps K] [--seed S] [--out FILE]`: the session machine
(`CairnAtproto.Session`) run against the fake PDS and its host (`CairnAtproto.Fake.World`), in
random sequences: sign-ins (right and wrong passwords), resumes, calls, cancels, sign-outs;
replies in any order, lost after the server handled them, or failed before it saw them; posts
arriving, tokens expiring and revoked, faults and delays. Requests are Cairn's `Request.http`, and
the host (`World.send`) attaches each one's Keychain secret and captures what it asks.

It is the check `atproto.no-token` of `cairn_atproto^15` ("No Lean value holds a token"). Every
token the fake issues is a marker string, and after every step it searches every Lean value the
step touched for one: the reply handed to the session, the session's state, and everything it
put out (requests, answers and the replies in them, events). With the host's capture working, a
marker reaches Lean only if a request that is answered with tokens doesn't capture them.

To show the search finds what it looks for, the same sequences are run once more with the
host's capture off; that run must find markers. It also decodes every 2xx `getTimeline` answer
with `FeedPage.ofJson`, and checks that a cancelled call is never answered. Exit 0 iff no marker
reached Lean, the control run found one, every page decoded and no cancelled call was
answered.

The sequences also write (putRecord, deleteRecord, mute, unmute, updateSeen) and read
(getPosts, notifications, profiles), with other accounts acting, the AppView lagging and
writes failing (400 before, lost after). They run the checks of the assumptions
`cairn_atproto^22`–`^25` against the fake, each of which must see cases and no violation:

* `atproto.idempotent-writes` (^22): a 2xx write sent again (on a copy of the world) leaves the
  repo, mutes and seenAt as they were;
* `atproto.read-your-writes` (^23): after a 2xx putRecord, getRecord (on a copy) answers the
  record written; after a 2xx deleteRecord, RecordNotFound; whatever the AppView's lag;
* `atproto.count-viewer` (^24): every post view the app is handed (timeline, getPosts) has the
  like and repost counts of the moment it was served, the tester's own exactly when `viewer`
  says so;
* `atproto.expired-not-applied` (^25): a write answered 400 ExpiredToken changed nothing.

The real network's half of each is cairn#258. -/

open CairnJson CairnAtproto CairnAtproto.Session CairnAtproto.Fake Cairn.Fuzz

structure Stats where
  steps : Nat := 0
  sends : Nat := 0
  served : Nat := 0
  lost : Nat := 0
  failedBefore : Nat := 0
  markersIssued : Nat := 0
  leaks : Nat := 0
  signedIn : Nat := 0
  refreshed : Nat := 0
  refreshFailed : Nat := 0
  refused : Nat := 0
  expiredSeen : Nat := 0
  pages : Nat := 0
  posts : Nat := 0
  badPages : Nat := 0
  notFound : Nat := 0
  cancels : Nat := 0
  cancelledRequests : Nat := 0
  answeredAfterCancel : Nat := 0
  firstLeak : Option String := none
  /-- `atproto.idempotent-writes`: 2xx writes sent again, and those that changed something. -/
  idem : Nat := 0
  idemBad : Nat := 0
  /-- `atproto.read-your-writes`: 2xx puts and deletes read back, and those read wrong. -/
  ryw : Nat := 0
  rywBad : Nat := 0
  /-- `atproto.count-viewer`: post views checked, and those whose counts and viewer disagree. -/
  views : Nat := 0
  viewsBad : Nat := 0
  /-- `atproto.expired-not-applied`: writes refused with ExpiredToken, and those applied. -/
  expiredWrites : Nat := 0
  expiredBad : Nat := 0
  /-- 2xx writes, by NSID's last segment. -/
  writes : Nat := 0
  firstBad : Option String := none
deriving Repr, Inhabited

def Stats.add (a b : Stats) : Stats :=
  { steps := a.steps + b.steps, sends := a.sends + b.sends, served := a.served + b.served,
    lost := a.lost + b.lost, failedBefore := a.failedBefore + b.failedBefore,
    markersIssued := a.markersIssued + b.markersIssued, leaks := a.leaks + b.leaks,
    signedIn := a.signedIn + b.signedIn, refreshed := a.refreshed + b.refreshed,
    refreshFailed := a.refreshFailed + b.refreshFailed, refused := a.refused + b.refused,
    expiredSeen := a.expiredSeen + b.expiredSeen, pages := a.pages + b.pages,
    posts := a.posts + b.posts, badPages := a.badPages + b.badPages,
    notFound := a.notFound + b.notFound, cancels := a.cancels + b.cancels,
    cancelledRequests := a.cancelledRequests + b.cancelledRequests,
    answeredAfterCancel := a.answeredAfterCancel + b.answeredAfterCancel, firstLeak := a.firstLeak.or b.firstLeak,
    idem := a.idem + b.idem, idemBad := a.idemBad + b.idemBad, ryw := a.ryw + b.ryw,
    rywBad := a.rywBad + b.rywBad, views := a.views + b.views, viewsBad := a.viewsBad + b.viewsBad,
    expiredWrites := a.expiredWrites + b.expiredWrites, expiredBad := a.expiredBad + b.expiredBad,
    writes := a.writes + b.writes, firstBad := a.firstBad.or b.firstBad }

structure Run where
  s : State := init
  w : World
  /-- Requests the session sent that the host hasn't answered: id, request. -/
  pending : List (Nat × Cairn.Request) := []
  /-- The app's calls it cancelled. -/
  cancelled : List Nat := []
  /-- The app's calls: id, call. -/
  calls : List (Nat × Call) := []
  nextCall : Nat := 0
  cursor : Option String := none
  /-- Posts from the pages read: what writes like and repost. -/
  posts : List StrongRef := []
  st : Stats := {}

/-- Whether an `Out` holds a marker: its text, and the bytes of any reply in it. -/
def outLeaks : Out → Bool
  | .answer _ (.reply r) => replyHasMarker r
  | .event (.signInFailed r) | .event (.refreshFailed r) => replyHasMarker r
  | _ => false

def Run.note (r : Run) (what : String) (leak : Bool) : Run :=
  if leak then { r with st := { r.st with leaks := r.st.leaks + 1,
                                          firstLeak := r.st.firstLeak.or (some what) } }
  else r

/-! ## The assumptions' checks (cairn_atproto^22–^25), against the fake -/

def writeNsids : List String :=
  [nsidPutRecord, nsidDeleteRecord, nsidMuteActor, nsidUnmuteActor, nsidUpdateSeen]

/-- What a write can change: the tester's repo, mutes and seenAt. -/
def written (w : World) : List Rec × List String × Option Nat :=
  (w.server.now.repo, w.server.now.muted, w.server.seenAt)

/-- A copy of the world for a probe: no faults queued, no delay. -/
def calm (w : World) : World := { w with server := { w.server with faults := [], delayMs := 0 } }

def statusOf : Cairn.Reply → Option Nat
  | .http st _ _ => some st
  | _ => none

def errorName : Cairn.Reply → Option String
  | .http _ _ b => (decodeBytes b).bind (·.str? "error")
  | _ => none

def Stats.bad (st : Stats) (what : String) : Stats := { st with firstBad := st.firstBad.or (some what) }

/-- ^24: every post view in a 2xx answer has counts and viewer state from one moment: the
like count is the seeded likes plus every like record the AppView shows, the tester's among
them exactly when `viewer.like` is set (and the same for reposts). -/
def checkViews (w : World) (posts : List Post) (st : Stats) : Stats :=
  let s := w.server
  let f := s.seen
  posts.foldl (fun st p =>
    match s.postAt? p.uri with
    | none => st.bad s!"count-viewer: {p.uri} isn't a post"
    | some k =>
      let mineL := (f.myLikes p.uri).length
      let mineR := (f.myReposts p.uri).length
      let ok := p.likeCount == seededLikes s.cfg k + (f.likes.filter (·.2 == p.uri)).length + mineL &&
        p.repostCount == seededReposts s.cfg k + (f.reposts.filter (·.2 == p.uri)).length + mineR &&
        p.viewer.like.isSome == (mineL > 0) && p.viewer.repost.isSome == (mineR > 0)
      let st := { st with views := st.views + 1 }
      if ok then st else { st.bad s!"count-viewer: {p.uri}" with viewsBad := st.viewsBad + 1 }) st

def feedPosts (p : FeedPage) : List Post :=
  p.feed.flatMap fun it => it.post :: (match it.reply with
    | some r => (match r.root with | .post q => [q] | _ => []) ++ (match r.parent with | .post q => [q] | _ => [])
    | none => [])

/-- The checks on request `h`, served from `before` to `after` with reply `rep`. -/
def checks (before after : World) (h : Cairn.Request) (rep : Cairn.Reply) (st : Stats) : Stats :=
  match h with
  | .http _ url hs body t secret .. =>
    let nsid := nsidOf url
    let body := (String.fromUTF8? body).getD ""
    let ok := (statusOf rep).any isSuccess
    -- ^25: a write refused with ExpiredToken changed nothing.
    let st := if writeNsids.contains nsid && isExpired rep then
        let st := { st with expiredWrites := st.expiredWrites + 1 }
        if written before == written after then st
        else { st.bad s!"expired-not-applied: {nsid} {body}" with expiredBad := st.expiredBad + 1 }
      else st
    -- ^22: a 2xx write sent again changes nothing.
    let st := if writeNsids.contains nsid && ok then
        let st := { st with writes := st.writes + 1 }
        let (again, rep2) := (calm after).send h
        if (statusOf rep2).any isSuccess then
          let st := { st with idem := st.idem + 1 }
          if written again == written after then st
          else { st.bad s!"idempotent-writes: {nsid} {body}" with idemBad := st.idemBad + 1 }
        else st
      else st
    -- ^23: after a 2xx put or delete, getRecord reads it back (the AppView may lag).
    let readBack (u : AtUri) (expect : Option Record) : Stats :=
      let get := Cairn.Request.http "GET" (xrpcUrl (originOf url) nsidGetRecord (getRecordParams u)) hs
        ByteArray.empty t secret
      let rep2 := ((calm after).send get).2
      let found := match rep2 with
        | .http st2 _ b => if isSuccess st2 then some ((decodeBytes b).bind RecordView.ofJson) else none
        | _ => none
      let notFound := errorName rep2 == some "RecordNotFound"
      if found.isNone && !notFound then st
      else
        let st := { st with ryw := st.ryw + 1 }
        let good := match expect, found with
          | some r, some (some v) => v.value == r && v.uri == s!"at://{u.repo}/{u.collection}/{u.rkey}"
          | none, none => notFound
          | _, _ => false
        if good then st else { st.bad s!"read-your-writes: {nsid} {body}" with rywBad := st.rywBad + 1 }
    let st := if ok && nsid == nsidPutRecord then
        match (decode body).bind PutRecord.ofJson with
        | some w => readBack w.uri (some w.record)
        | none => st
      else if ok && nsid == nsidDeleteRecord then
        match (decode body).bind deleteRecordOf with
        | some u => readBack u none
        | none => st
      else st
    st
  | _ => st

/-- A call's answer: a 2xx `getTimeline` page must decode. Its post views, and a `getPosts`
answer's, are checked against the world it came from (^24, `checkViews`): the session hands an
answer over in the step its reply arrives. -/
def Run.page (r : Run) (id : Nat) (rep : Cairn.Reply) : Run :=
  let views (posts : List Post) (r : Run) : Run :=
    if r.w.captures then { r with st := checkViews r.w posts r.st } else r
  match r.calls.lookup id, rep with
  | some c, .http st _ body =>
    if c.nsid == nsidGetPosts && isSuccess st then
      match (decodeBytes body).bind Posts.ofJson with
      | some p => views p.posts r
      | none => { r with st := { r.st with badPages := r.st.badPages + 1 } }
    else if c.nsid == nsidGetTimeline && isSuccess st then
      match (decodeBytes body).bind FeedPage.ofJson with
      | some p =>
        let seen := p.feed.map fun it => ({ uri := it.post.uri, cid := it.post.cid } : StrongRef)
        views (feedPosts p) { r with cursor := p.cursor.or r.cursor, posts := (seen ++ r.posts).take 40,
                                     st := { r.st with pages := r.st.pages + 1, posts := r.st.posts + p.feed.length } }
      | none => { r with st := { r.st with badPages := r.st.badPages + 1 } }
    else r
  | _, _ => r

/-- What the session put out: requests to the host, forgets and cancels done at once, answers
read. -/
def Run.absorb (r : Run) (outs : List Out) : Run :=
  outs.foldl (fun r o =>
    let r := r.note s!"out {(reprStr o).take 300}" (hasMarker (reprStr o) || outLeaks o)
    match o with
    | .send rid _ h => { r with pending := r.pending ++ [(rid, h)], st := { r.st with sends := r.st.sends + 1 } }
    | .forget _ item => { r with w := r.w.forget item }
    | .cancel rid =>
      -- The runtime drops the request: never answered (the server may already have it).
      { r with pending := r.pending.filter (·.1 != rid),
               st := { r.st with cancelledRequests := r.st.cancelledRequests + 1 } }
    | .answer id _ =>
      let r := if r.cancelled.contains id then
          { r with st := { r.st with answeredAfterCancel := r.st.answeredAfterCancel + 1 } }
        else r
      match o with
      | .answer id (.reply rep) => r.page id rep
      | _ => r
    | .event (.signedIn _) => { r with st := { r.st with signedIn := r.st.signedIn + 1 } }
    | .event (.refreshed _) => { r with st := { r.st with refreshed := r.st.refreshed + 1 } }
    | .event (.refreshFailed _) => { r with st := { r.st with refreshFailed := r.st.refreshFailed + 1 } }
    | .event (.signedOut .refused) => { r with st := { r.st with refused := r.st.refused + 1 } }
    | _ => r) r

/-- Feed the session one input, then check every Lean value the step touched. -/
def Run.feed (r : Run) (i : Input) : Run :=
  let r := r.note s!"input {(reprStr i).take 300}" (match i with
    | .reply _ rep => replyHasMarker rep
    | _ => hasMarker (reprStr i))
  let (s, outs) := step r.s i
  let r := { r with s, st := { r.st with steps := r.st.steps + 1 } }
  let r := r.note s!"state {(reprStr s).take 300}" (hasMarker (reprStr s))
  r.absorb outs

def Run.call (r : Run) (c : Call) : Run :=
  let id := r.nextCall
  { r with nextCall := id + 1, calls := (id, c) :: r.calls }.feed (.call id c)

/-- The host answers pending request `k`: served, lost after the server handled it, or failed
before it got there. -/
def Run.answer (r : Run) (k : Nat) (how : Nat) : Run :=
  match r.pending[k]? with
  | none => r
  | some (rid, h) =>
    let r := { r with pending := r.pending.eraseIdx k }
    let issuedBefore := r.w.server.issued
    let (w, rep, st) :=
      if how = 0 then
        let (w, rep) := r.w.send h
        (w, rep, { r.st with served := r.st.served + 1 })
      else if how = 1 then
        let (w, rep) := r.w.send h (lose := true)
        (w, rep, { r.st with lost := r.st.lost + 1 })
      else (r.w, .failed .network "The network connection was lost.",
            { r.st with failedBefore := r.st.failedBefore + 1 })
    let st := if how = 0 && r.w.captures then checks r.w w h rep st else st
    let st := { st with markersIssued := st.markersIssued + 2 * (w.server.issued - issuedBefore),
                        expiredSeen := st.expiredSeen + (if isExpired rep then 1 else 0),
                        notFound := st.notFound + (match rep with | .failed .notFound _ => 1 | _ => 0) }
    { r with w, st }.feed (.reply rid rep)

def Run.op (r : Run) : Gen Run := do
  let c := r.w.server.cfg
  let hasPending := !r.pending.isEmpty
  let choice ← Gen.weighted [
    (6, pure 0), (2, pure 1), (14, pure 2), (3, pure 3), (2, pure 4),
    (if hasPending then 34 else 0, pure 5), (if hasPending then 3 else 0, pure 6),
    (if hasPending then 3 else 0, pure 7), (6, pure 8), (if r.calls.isEmpty then 0 else 3, pure 9),
    (10, pure 10), (5, pure 11)]
  match choice with
  | 0 =>
    let pw := if ← Gen.chance 3 4 then c.password else "wrong-pass-word-0000"
    return r.feed (.signIn c.service c.identifier pw)
  | 1 => return r.feed (.resume c.service)
  | 2 =>
    let limit ← Gen.oneOf [pure none, (some ·) <$> Gen.range 1 100]
    let cursor := if ← Gen.bool then r.cursor else none
    return r.call (Call.getTimeline limit cursor)
  | 3 => return r.call Call.getSession
  | 4 => return r.feed .signOut
  | 5 => return r.answer (← Gen.below r.pending.length) 0
  | 6 => return r.answer (← Gen.below r.pending.length) 1
  | 7 => return r.answer (← Gen.below r.pending.length) 2
  | 9 =>
    -- Cancel one of the latest calls (in flight, held, or already answered).
    let ids := (r.calls.take 4).map (·.1)
    if ids.isEmpty then return r
    let id ← Gen.elem ids
    let r := { r with cancelled := id :: r.cancelled, st := { r.st with cancels := r.st.cancels + 1 } }
    -- An answer already given doesn't count against it: only answers after the cancel do.
    return r.feed (.cancel [id])
  | 10 =>
    -- A write: a few record keys, so writes repeat and deletes find (or miss) them.
    let rkey ← Gen.elem ["3l2aaaaaaaa2a", "3l2aaaaaaaa3b", "3l2aaaaaaaa4c"]
    let post ← if r.posts.isEmpty then pure { uri := postUri c 0, cid := postCid c 0 } else Gen.elem r.posts
    let at_ ← Gen.elem ["2026-10-02T00:00:00.000Z", "2026-10-03T00:00:00.000Z"]
    let actor ← Gen.elem (authorNames.map fun (h, _) => s!"{h}.fake.test")
    let record ← Gen.elem [Record.like post at_, .like post at_, .repost post at_,
      .follow s!"did:plc:fakeauthor{(actor.splitOn ".").headD ""}" at_]
    let w : PutRecord := { repo := c.did, rkey, record }
    let call ← Gen.oneOf [pure (Call.putRecord w), pure (Call.putRecord w), pure (Call.deleteRecord w.uri),
      pure (Call.muteActor actor), pure (Call.unmuteActor actor),
      Call.updateSeen <$> Gen.elem ["2026-10-01T00:00:00.000Z", "2026-10-02T00:00:00.000Z"]]
    return r.call call
  | 11 =>
    let uris := r.posts.take 5 |>.map (·.uri)
    let call ← Gen.oneOf [pure (Call.getPosts uris), pure (Call.getPosts uris),
      pure (Call.listNotifications (some 10) none), pure Call.getUnreadCount,
      pure (Call.getProfile c.identifier), pure (Call.getProfile "ada.fake.test")]
    return r.call call
  | _ =>
    let ctl ← Gen.oneOf [
      do return .act (← Gen.elem [.like, .repost, .follow]) (← Gen.below authorNames.length) none,
      (Control.lag ·) <$> Gen.elem [0, 2, 5], pure .catchup,
      do return .fail (← Gen.range 1 2) (← Gen.elem [.refused, .lostAfter]),
      (Control.post ·) <$> Gen.range 1 20, pure .expire, pure .expire, pure .revoke,
      do return .fail (← Gen.range 1 3) (← Gen.elem [.internal, .unavailable, .rateLimit, .timeout]),
      (Control.slow ·) <$> Gen.elem [0, 0, 300]]
    return { r with w := { r.w with server := r.w.server.control ctl } }

def runOps : Nat → Run → Gen Run
  | 0, r => pure r
  | n + 1, r => do runOps n (← r.op)

/-- One sequence, then the host answers everything still pending. -/
def sequence (cfg : Config) (captures : Bool) (steps : Nat) : Gen Stats := do
  let r : Run := { w := { World.init cfg with captures } }
  let r ← runOps steps r
  let drain := (List.range (r.pending.length + 64)).foldl (fun r _ =>
    if r.pending.isEmpty then r else r.answer 0 0) r
  return drain.st

def flag (args : List String) (name : String) (d : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD d
  | _ => d

def strFlag (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

def runAll (seed sequences steps : Nat) (captures : Bool) : Stats :=
  (List.range sequences).foldl (fun acc i =>
    let g := Rng.ofSeed (seed * 1000003 + i)
    let (cfgSeed, g) := (Gen.below 1000000).run g
    let (base, g) := (Gen.range 0 60).run g
    let (life, g) := (Gen.range 1 8).run g
    let (arrival, g) := (Gen.elem [0, 2, 3, 5]).run g
    let (act, g) := (Gen.elem [0, 2, 4, 8]).run g
    let (lag, g) := (Gen.elem [0, 1, 2, 5]).run g
    let cfg : Config := { seed := cfgSeed, service := "http://127.0.0.1:2583", base, life, arrival, act, lag }
    acc.add ((sequence cfg captures steps).run' g)) {}

def statsJson (s : Stats) : Json :=
  .obj [("steps", Json.ofNat s.steps), ("sends", Json.ofNat s.sends), ("served", Json.ofNat s.served),
    ("lost", Json.ofNat s.lost), ("failedBefore", Json.ofNat s.failedBefore),
    ("markersIssued", Json.ofNat s.markersIssued), ("leaks", Json.ofNat s.leaks),
    ("signedIn", Json.ofNat s.signedIn), ("refreshed", Json.ofNat s.refreshed),
    ("refreshFailed", Json.ofNat s.refreshFailed), ("refused", Json.ofNat s.refused),
    ("expiredToken", Json.ofNat s.expiredSeen), ("notFound", Json.ofNat s.notFound),
    ("pages", Json.ofNat s.pages), ("posts", Json.ofNat s.posts), ("badPages", Json.ofNat s.badPages),
    ("cancels", Json.ofNat s.cancels), ("cancelledRequests", Json.ofNat s.cancelledRequests),
    ("answeredAfterCancel", Json.ofNat s.answeredAfterCancel), ("writes", Json.ofNat s.writes)]

/-- The assumptions' checks: name, claim, cases, violations. -/
def assumeChecks (s : Stats) : List (String × String × Nat × Nat) :=
  [("atproto.idempotent-writes", "cairn_atproto^22", s.idem, s.idemBad),
   ("atproto.read-your-writes", "cairn_atproto^23", s.ryw, s.rywBad),
   ("atproto.count-viewer", "cairn_atproto^24", s.views, s.viewsBad),
   ("atproto.expired-not-applied", "cairn_atproto^25", s.expiredWrites, s.expiredBad)]

def main (args : List String) : IO UInt32 := do
  let sequences := flag args "--sequences" 300
  let steps := flag args "--steps" 80
  let seed := flag args "--seed" 0
  let s := runAll seed sequences steps true
  let control := runAll seed sequences steps false
  let noToken := s.leaks == 0 && control.leaks > 0 && s.badPages == 0 && s.markersIssued > 0 &&
    s.answeredAfterCancel == 0 && s.cancelledRequests > 0
  let assumed := assumeChecks s
  let ok := noToken && assumed.all fun (_, _, n, bad) => n > 0 && bad == 0
  if let some out := strFlag args "--out" then
    IO.FS.writeFile out (encode (.obj [("check", .str "atproto.no-token"), ("claim", .str "cairn_atproto^15"),
      ("seed", Json.ofNat seed), ("sequences", Json.ofNat sequences), ("steps", Json.ofNat steps),
      ("ok", .bool noToken), ("run", statsJson s), ("controlRun", statsJson control),
      ("assumptions", .arr (assumed.map fun (name, claim, n, bad) => .obj [("check", .str name),
        ("claim", .str claim), ("cases", Json.ofNat n), ("violations", Json.ofNat bad),
        ("ok", .bool (n > 0 && bad == 0))]))]) ++ "\n")
  IO.println s!"atproto.no-token (cairn_atproto^15): {sequences} sequences × {steps} steps, seed {seed}"
  IO.println s!"  {s.steps} session steps, {s.sends} requests ({s.served} served, {s.lost} lost after the server, {s.failedBefore} failed before it), {s.markersIssued} token markers issued"
  IO.println s!"  {s.signedIn} sign-ins, {s.expiredSeen} ExpiredToken, {s.refreshed} refreshes, {s.refreshFailed} failed, {s.refused} refused; {s.notFound} missing items; {s.pages} pages ({s.posts} posts) decoded, {s.badPages} not"
  IO.println s!"  {s.cancels} cancels ({s.cancelledRequests} requests cancelled), {s.answeredAfterCancel} answered after their cancel"
  IO.println s!"  markers in Lean values: {s.leaks}{match s.firstLeak with | some w => s!" (first: {w})" | none => ""}"
  IO.println s!"  control run, the host's capture off: {control.leaks} found (must be > 0)"
  IO.println (if noToken then "atproto.no-token: ok" else "atproto.no-token: FAILED")
  IO.println s!"  {s.writes} writes acknowledged"
  for (name, claim, n, bad) in assumed do
    IO.println s!"{name} ({claim}): {n} cases, {bad} violations: {if n > 0 && bad == 0 then "ok" else "FAILED"}"
  if let some w := s.firstBad then IO.println s!"  first violation: {w}"
  return if ok then 0 else 1
