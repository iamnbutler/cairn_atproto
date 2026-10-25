import CairnAtproto

/-! `lake exe fake-fuzz [--sequences N] [--steps K] [--seed S] [--out FILE]`: the session machine
(`CairnAtproto.Session`) run against the fake PDS and its host (`CairnAtproto.Fake.World`), in
random sequences: sign-ins (right and wrong passwords), resumes, calls, sign-outs; replies in any
order, lost after the server handled them, or failed before it saw them; posts arriving, tokens
expiring and revoked, faults and delays.

It is the check `atproto.no-token` of `cairn_atproto^10` ("No Lean value holds a token"). Every
token the fake issues is a marker string, and after every step it searches every Lean value the
step touched for one: the reply handed to the session, the session's state, and everything it
put out (requests, answers and the replies in them, events). With the host's capture working, a
marker reaches Lean only if a request that is answered with tokens doesn't capture them.

To show the search finds what it looks for, the same sequences are run once more with the
host's capture off; that run must find markers. It also decodes every 2xx `getTimeline` answer
with `FeedPage.ofJson`. Exit 0 iff no marker reached Lean, the control run found one, and every
page decoded. -/

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
  firstLeak : Option String := none
deriving Repr, Inhabited

def Stats.add (a b : Stats) : Stats :=
  { steps := a.steps + b.steps, sends := a.sends + b.sends, served := a.served + b.served,
    lost := a.lost + b.lost, failedBefore := a.failedBefore + b.failedBefore,
    markersIssued := a.markersIssued + b.markersIssued, leaks := a.leaks + b.leaks,
    signedIn := a.signedIn + b.signedIn, refreshed := a.refreshed + b.refreshed,
    refreshFailed := a.refreshFailed + b.refreshFailed, refused := a.refused + b.refused,
    expiredSeen := a.expiredSeen + b.expiredSeen, pages := a.pages + b.pages,
    posts := a.posts + b.posts, badPages := a.badPages + b.badPages,
    notFound := a.notFound + b.notFound, firstLeak := a.firstLeak.or b.firstLeak }

structure Run where
  s : State := init
  w : World
  /-- Requests the session sent that the host hasn't answered: id, request. -/
  pending : List (Nat × Http) := []
  /-- The app's calls: id, call. -/
  calls : List (Nat × Call) := []
  nextCall : Nat := 0
  cursor : Option String := none
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

/-- What the session put out: requests to the host, forgets done at once, answers read. -/
def Run.absorb (r : Run) (outs : List Out) : Run :=
  outs.foldl (fun r o =>
    let r := r.note s!"out {(reprStr o).take 300}" (hasMarker (reprStr o) || outLeaks o)
    match o with
    | .send rid _ h => { r with pending := r.pending ++ [(rid, h)], st := { r.st with sends := r.st.sends + 1 } }
    | .forget _ item => { r with w := r.w.forget item }
    | .event (.signedIn _) => { r with st := { r.st with signedIn := r.st.signedIn + 1 } }
    | .event (.refreshed _) => { r with st := { r.st with refreshed := r.st.refreshed + 1 } }
    | .event (.refreshFailed _) => { r with st := { r.st with refreshFailed := r.st.refreshFailed + 1 } }
    | .event (.signedOut .refused) => { r with st := { r.st with refused := r.st.refused + 1 } }
    | .answer id (.reply rep) =>
      match r.calls.lookup id, rep with
      | some c, .http st _ body =>
        if c.nsid == nsidGetTimeline && isSuccess st then
          match (decodeBytes body).bind FeedPage.ofJson with
          | some p => { r with cursor := p.cursor.or r.cursor,
                               st := { r.st with pages := r.st.pages + 1, posts := r.st.posts + p.feed.length } }
          | none => { r with st := { r.st with badPages := r.st.badPages + 1 } }
        else r
      | _, _ => r
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
    (if hasPending then 3 else 0, pure 7), (6, pure 8)]
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
  | _ =>
    let ctl ← Gen.oneOf [
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
    let cfg : Config := { seed := cfgSeed, service := "http://127.0.0.1:2583", base, life, arrival }
    acc.add ((sequence cfg captures steps).run' g)) {}

def statsJson (s : Stats) : Json :=
  .obj [("steps", Json.ofNat s.steps), ("sends", Json.ofNat s.sends), ("served", Json.ofNat s.served),
    ("lost", Json.ofNat s.lost), ("failedBefore", Json.ofNat s.failedBefore),
    ("markersIssued", Json.ofNat s.markersIssued), ("leaks", Json.ofNat s.leaks),
    ("signedIn", Json.ofNat s.signedIn), ("refreshed", Json.ofNat s.refreshed),
    ("refreshFailed", Json.ofNat s.refreshFailed), ("refused", Json.ofNat s.refused),
    ("expiredToken", Json.ofNat s.expiredSeen), ("notFound", Json.ofNat s.notFound),
    ("pages", Json.ofNat s.pages), ("posts", Json.ofNat s.posts), ("badPages", Json.ofNat s.badPages)]

def main (args : List String) : IO UInt32 := do
  let sequences := flag args "--sequences" 300
  let steps := flag args "--steps" 80
  let seed := flag args "--seed" 0
  let s := runAll seed sequences steps true
  let control := runAll seed sequences steps false
  let ok := s.leaks == 0 && control.leaks > 0 && s.badPages == 0 && s.markersIssued > 0
  if let some out := strFlag args "--out" then
    IO.FS.writeFile out (encode (.obj [("check", .str "atproto.no-token"), ("claim", .str "cairn_atproto^10"),
      ("seed", Json.ofNat seed), ("sequences", Json.ofNat sequences), ("steps", Json.ofNat steps),
      ("ok", .bool ok), ("run", statsJson s), ("controlRun", statsJson control)]) ++ "\n")
  IO.println s!"atproto.no-token (cairn_atproto^10): {sequences} sequences × {steps} steps, seed {seed}"
  IO.println s!"  {s.steps} session steps, {s.sends} requests ({s.served} served, {s.lost} lost after the server, {s.failedBefore} failed before it), {s.markersIssued} token markers issued"
  IO.println s!"  {s.signedIn} sign-ins, {s.expiredSeen} ExpiredToken, {s.refreshed} refreshes, {s.refreshFailed} failed, {s.refused} refused; {s.notFound} missing items; {s.pages} pages ({s.posts} posts) decoded, {s.badPages} not"
  IO.println s!"  markers in Lean values: {s.leaks}{match s.firstLeak with | some w => s!" (first: {w})" | none => ""}"
  IO.println s!"  control run, the host's capture off: {control.leaks} found (must be > 0)"
  IO.println (if ok then "atproto.no-token: ok" else "atproto.no-token: FAILED")
  return if ok then 0 else 1
