module

public import CairnAtproto.Session
public import Cairn.Fuzz.Rng
public import CairnAtproto.Datetime

/-! # A fake PDS

A model of the part of a Bluesky PDS that M4 talks to, so nothing needs the network to be
tested (cairn#208). The same behaviour runs over HTTP in `tools/fake-pds/` (Bun), and
`tools/fake-pds/replay.ts` checks that the two agree request by request.

* **The timeline** only grows at its head. Post `k` (from the oldest, `0`) is a pure function of
  the seed and `k` (`postAt`), so a post never changes once it is there, and between requests new
  ones arrive at the head at random (`arrivals`), or when asked (`Control.post`).
* **`getTimeline`** pages from the head by an opaque cursor: a page of `limit` posts, newest
  first, and the cursor of its oldest post when there are older ones (none at the end). A
  cursor stays valid however many posts arrive after it.
* **Sessions.** `createSession` checks the one identifier and app password the seed gives
  (`Config.identifier`, `Config.password`) and issues a token *generation*: an access and a
  refresh token. The access token serves a random number of calls (1 to `Config.life`), then
  answers `ExpiredToken`; `refreshSession` with the current refresh token rotates both, and the
  old refresh token is refused from then on (`InvalidToken`). A token is a marker string
  (`fakepds-token.<kind>.<generation>.<nonce>`), never a secret, so a fuzz can check that none
  reaches Lean (`hasMarker`).
* **Faults** (`Control.fail`): the next calls answer 500, 503 or 429 `RateLimitExceeded`, or
  never answer (the client times out); `Control.slow` delays every reply.
* **The host** (`World`): its Keychain (which token each item holds) and its capture of
  `accessJwt` and `refreshJwt` (cairn#205's rules: a 2xx JSON object, all or nothing, the fields
  blanked), modelled over the server, so the session machine can be run against it.
* **For `cairn fuzz`** (`replies`): a `Cairn.Fuzz.Custom.replies` generator. Cairn's hook keeps no
  state between replies, so it answers what this server would in a state drawn at random that
  fits the request: the timeline as it stands at that request id, the access token expired with
  chance `1/life` (expiry after a random number of calls is memoryless), a refresh refused one
  time in ten (a rotation the host never captured), faults one time in eight.

Everything is total and pure; nothing here touches the network. -/

@[expose] public section

namespace CairnAtproto.Fake
open CairnJson CairnAtproto Cairn.Fuzz

/-! ## Seeded choices

SplitMix64 (`Cairn.Fuzz.Rng.mix`), keyed by the seed, a tag for what is being chosen and an
index. `tools/fake-pds/model.ts` computes the same numbers with `BigInt`. -/

def hash (seed tag i : Nat) : UInt64 :=
  Rng.mix (Rng.mix (seed.toUInt64 + tag.toUInt64 * Rng.golden) + i.toUInt64 * Rng.golden)

/-- A number below `n` (for `n > 0`). -/
def pick (seed tag i n : Nat) : Nat := (hash seed tag i).toNat % n

def padLeft (w : Nat) (c : Char) (s : String) : String :=
  String.ofList (List.replicate (w - s.length) c) ++ s

def hex16 (x : UInt64) : String := padLeft 16 '0' (String.ofList (Nat.toDigits 16 x.toNat))

def alphabet : List Char := "abcdefghijklmnopqrstuvwxyz234567".toList

/-- `n` characters of `alphabet`. -/
def code (seed tag n : Nat) : String :=
  String.ofList ((List.range n).map fun i => alphabet.getD (pick seed tag i 32) 'a')

/-- A decimal number: digits only, at most `max` of them. -/
def digits (max : Nat) (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || cs.length > max || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)

/-! ## The server's configuration -/

structure Config where
  seed : Nat := 0
  /-- Where the server is: image URLs and the DID document's PDS point here. -/
  service : String := "http://127.0.0.1:2583"
  /-- Posts on the timeline at the start. -/
  base : Nat := 40
  /-- After each XRPC request, 1 to 3 posts arrive with chance `1/arrival` (`0`: never). -/
  arrival : Nat := 3
  /-- An access token serves 1 to `life` calls (at least 1). -/
  life : Nat := 6
deriving Repr, DecidableEq, Inhabited

/-- The one test identifier the server accepts (a handle). -/
def Config.identifier (c : Config) : String := s!"tester-{code c.seed 40 4}.fake.test"
/-- Its app password, in Bluesky's `xxxx-xxxx-xxxx-xxxx` form. -/
def Config.password (c : Config) : String :=
  "-".intercalate [code c.seed 41 4, code c.seed 42 4, code c.seed 43 4, code c.seed 44 4]
/-- Ends every token, so a token from another seed is refused. -/
def Config.nonce (c : Config) : String := code c.seed 45 8
def Config.did (c : Config) : String := s!"did:plc:{code c.seed 46 24}"
def Config.email (c : Config) : String := s!"tester-{code c.seed 40 4}@example.test"
def Config.lifeOf (c : Config) (gen : Nat) : Nat := 1 + pick c.seed 20 gen (max c.life 1)

/-- The posts that arrive after XRPC request `n`. -/
def arrivals (c : Config) (n : Nat) : Nat :=
  if c.arrival = 0 then 0
  else if pick c.seed 30 n c.arrival = 0 then 1 + pick c.seed 31 n 3 else 0

/-- The posts that arrived before request `n`. -/
def arrivedBefore (c : Config) (n : Nat) : Nat := ((List.range n).map (arrivals c)).sum

/-! ## Dates -/

/-- 2026-10-01T00:00:00Z, in milliseconds: post `0`'s minute. -/
def epoch : Nat := 1790812800000

/-- Year, month and day of a day number counted from 1970-01-01 (Hinnant's `civil_from_days`). -/
def civil (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m, d)

/-- UTC milliseconds since the epoch as `YYYY-MM-DDTHH:MM:SS.mmmZ` (JavaScript's
`toISOString`). -/
def iso (ms : Nat) : String :=
  let (y, mo, d) := civil (ms / 86400000)
  let r := ms % 86400000
  let p (w n : Nat) := padLeft w '0' (toString n)
  s!"{p 4 y}-{p 2 mo}-{p 2 d}T{p 2 (r / 3600000)}:{p 2 (r / 60000 % 60)}:{p 2 (r / 1000 % 60)}.{p 3 (r % 1000)}Z"

/-! ## The timeline -/

def authorNames : List (String × String) :=
  [("ada", "Ada Lovelace"), ("zoe", "Zoë Ångström"), ("lei", "李雷"), ("sam", "Sam 🌊"),
   ("noor", "Noor"), ("kit", "Kit O'Hara \"KO\"")]

def words : List String :=
  ["the", "sea", "is", "calm", "tonight", "café", "naïve", "日本語", "テスト", "🌊", "🦋", "✨",
   "résumé", "über", "fjord", "lantern", "quiet", "river", "stone", "cairn", "path", "north",
   "light", "paper", "ink", "bread", "tea", "window", "rain", "→", "“quoted”", "a\\b", "tab\tsep",
   "new\nline", "<tag>", "&amp;", "100%", "#hash", "@ada.fake.test", "https://example.com/x?y=1&z=2"]

def imgUrl (c : Config) (w h : Nat) (name : String) : String :=
  s!"{trimService c.service}/img/{w}x{h}/{name}.png"

def author (c : Config) (i : Nat) : Profile :=
  let (h, d) := authorNames.getD i ("x", "x")
  { did := s!"did:plc:fakeauthor{h}", handle := s!"{h}.fake.test", displayName := some d,
    avatar := some (imgUrl c 96 96 s!"avatar-{h}") }

def authorOf (c : Config) (k : Nat) : Nat := pick c.seed 1 k authorNames.length
def createdMs (c : Config) (k : Nat) : Nat := epoch + k * 60000 + pick c.seed 5 k 59000
def rkey (k : Nat) : String := "3fk" ++ padLeft 8 '0' (toString k)
def postUri (c : Config) (k : Nat) : String :=
  s!"at://{(author c (authorOf c k)).did}/app.bsky.feed.post/{rkey k}"
def postCid (c : Config) (k : Nat) : String := "bafyreifake" ++ hex16 (hash c.seed 2 k)

def textOf (c : Config) (k : Nat) : String :=
  s!"#{k} " ++ " ".intercalate ((List.range (1 + pick c.seed 3 k 12)).map fun j =>
    words.getD (pick c.seed 4 (k * 16 + j) words.length) "")

def embedOf (c : Config) (k : Nat) : Option Embed :=
  match pick c.seed 10 k 8 with
  | 0 | 1 => some (.images ((List.range (1 + pick c.seed 11 k 4)).map fun i =>
      let w := 64 + pick c.seed 12 (k * 4 + i) 1200
      let h := 64 + pick c.seed 13 (k * 4 + i) 1200
      { thumb := imgUrl c w h s!"{k}-{i}", fullsize := imgUrl c w h s!"{k}-{i}",
        alt := s!"Image {i + 1} of post {k}", aspect := some (w, h) }))
  | 2 =>
    let e : External :=
      { uri := "https://example.com/fake/" ++ toString k, title := "Link " ++ toString k,
        description := textOf c (k + 1000000) }
    some (.external e)
  | _ => none

/-- Post `k`, counted from the oldest: a function of the seed and `k` only. -/
def postAt (c : Config) (k : Nat) : FeedItem :=
  let at_ := iso (createdMs c k)
  { post := { uri := postUri c k, cid := postCid c k, author := author c (authorOf c k),
              text := textOf c k, createdAt := at_, embed := embedOf c k,
              replyCount := pick c.seed 6 k 5, repostCount := pick c.seed 7 k 20,
              likeCount := pick c.seed 8 k 100, quoteCount := pick c.seed 9 k 3, indexedAt := at_ },
    reason := if pick c.seed 14 k 8 = 0
      then some (.repost (author c (pick c.seed 15 k authorNames.length)) at_) else none }

/-- The timeline of `length` posts, newest first, as `getTimeline` pages it. -/
def timeline (c : Config) (length : Nat) : List FeedItem :=
  (List.range length).reverse.map (postAt c)

/-- The cursor that asks for the posts older than post `k`: `<createdAt>::<cid>` of post `k`,
as the AppView's look. Opaque to clients. -/
def cursorOf (c : Config) (k : Nat) : String := s!"{iso (createdMs c k)}::{postCid c k}"

/-- The post a cursor names, if it is one this timeline of `length` posts gave out. -/
def cursorPos (c : Config) (length : Nat) (cur : String) : Option Nat :=
  match cur.splitOn "::" with
  | [t, _] =>
    match parseDatetime t with
    | some ms =>
      if ms < (epoch : Int) then none
      else
        let k := (ms - epoch).toNat / 60000
        if 0 < k && k < length && cursorOf c k == cur then some k else none
    | none => none
  | _ => none

/-- A page: `limit` posts older than post `before` (the head when `none`), newest first, and the
cursor of its oldest post unless it reached post `0`. -/
def page (c : Config) (length limit : Nat) (before : Option Nat) : FeedPage :=
  let hi := before.getD length
  let lo := hi - min limit hi
  { feed := (List.range (hi - lo)).map fun j => postAt c (hi - 1 - j),
    cursor := if lo = 0 then none else some (cursorOf c lo) }

/-! ## Requests and responses -/

/-- An HTTP request as the server sees it. -/
structure Req where
  method : String
  /-- The path and query: `/xrpc/app.bsky.feed.getTimeline?limit=3`. -/
  path : String
  authorization : Option String := none
  body : String := ""
deriving Repr, DecidableEq, Inhabited

inductive Response where
  /-- A JSON reply (`content-type: application/json`), after `delayMs`. -/
  | json (status : Nat) (headers : List (String × String)) (body : Json) (delayMs : Nat)
  /-- A PNG image `w` by `h`. -/
  | png (w h : Nat)
  /-- No reply at all: the client times out. -/
  | hang
deriving Repr, Inhabited

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `application/x-www-form-urlencoded` bytes: `+` is a space, `%XX` a byte. -/
def formBytes : List Char → List UInt8
  | '+' :: cs => 32 :: formBytes cs
  | '%' :: a :: b :: cs =>
    match hexVal a, hexVal b with
    | some x, some y => (x * 16 + y).toUInt8 :: formBytes cs
    | _, _ => 37 :: formBytes (a :: b :: cs)
  | c :: cs => (String.singleton c).toUTF8.toList ++ formBytes cs
  | [] => []

def formDecode (s : String) : String :=
  (String.fromUTF8? (ByteArray.mk (formBytes s.toList).toArray)).getD ""

/-- Split at the first `sep`. -/
def splitFirst (s sep : String) : String × Option String :=
  match s.splitOn sep with
  | [] => ("", none)
  | [a] => (a, none)
  | a :: rest => (a, some (sep.intercalate rest))

/-- The path and its query parameters, decoded (as `URLSearchParams` reads them). -/
def splitPath (p : String) : String × List (String × String) :=
  match splitFirst p "?" with
  | (path, none) => (path, [])
  | (path, some q) =>
    (path, (q.splitOn "&").filterMap fun kv =>
      if kv.isEmpty then none
      else match splitFirst kv "=" with
        | (k, v) => some (formDecode k, formDecode (v.getD "")))

def errJson (name msg : String) : Json := .obj [("error", .str name), ("message", .str msg)]

/-! ## The server -/

inductive Fault where
  /-- 500 `InternalServerError`. -/
  | internal
  /-- 503 `ServiceUnavailable`. -/
  | unavailable
  /-- 429 `RateLimitExceeded`, with `ratelimit-*` headers. -/
  | rateLimit
  /-- No answer: the client times out. -/
  | timeout
deriving Repr, DecidableEq, Inhabited

def Fault.ofString : String → Option Fault
  | "500" => some .internal
  | "503" => some .unavailable
  | "429" => some .rateLimit
  | "timeout" => some .timeout
  | _ => none

/-- The session the server holds: its token generation, how many calls its access token serves
and has served, and whether it was expired by hand. -/
structure Live where
  gen : Nat
  life : Nat
  uses : Nat := 0
  expired : Bool := false
deriving Repr, DecidableEq, Inhabited

structure Server where
  cfg : Config
  /-- Posts on the timeline. -/
  length : Nat
  /-- XRPC requests received. -/
  count : Nat := 0
  /-- Token generations issued. -/
  issued : Nat := 0
  live : Option Live := none
  /-- Faults for the next calls, in order. -/
  faults : List Fault := []
  /-- Every XRPC reply waits this long. -/
  delayMs : Nat := 0
deriving Repr, Inhabited

def Server.init (c : Config) : Server := { cfg := c, length := c.base }

def tokenPrefix : String := "fakepds-token"

/-- A token: a marker string, never a secret. -/
def token (c : Config) (kind : String) (gen : Nat) : String :=
  s!"{tokenPrefix}.{kind}.{gen}.{c.nonce}"

/-- A token's kind and generation, if this server issued it. -/
def parseToken (c : Config) (t : String) : Option (String × Nat) :=
  match t.splitOn "." with
  | [m, kind, g, n] =>
    if m == tokenPrefix && n == c.nonce && (kind == "access" || kind == "refresh")
    then (digits 9 g).map (kind, ·) else none
  | _ => none

def bearer (auth : Option String) : Option String :=
  auth.bind fun a => if a.startsWith "Bearer " then some (a.drop 7).toString else none

def Server.accountJson (s : Server) : List (String × Json) :=
  [("did", .str s.cfg.did), ("handle", .str s.cfg.identifier), ("email", .str s.cfg.email),
   ("active", .bool true), ("didDoc", didDocJson s.cfg.did (trimService s.cfg.service))]

/-- A new token generation; the reply that carries it. -/
def Server.issue (s : Server) : Server × Response :=
  let g := s.issued + 1
  ({ s with issued := g, live := some { gen := g, life := s.cfg.lifeOf g } },
   .json 200 [] (.obj ([("accessJwt", .str (token s.cfg "access" g)),
                        ("refreshJwt", .str (token s.cfg "refresh" g))] ++ s.accountJson)) s.delayMs)

def Server.fail (s : Server) (st : Nat) (name msg : String) : Response :=
  .json st [] (errJson name msg) s.delayMs

/-- The token the request carries, checked for kind `kind`: the session's generation, or why
not. An access token also counts the call, and is expired after `life` of them. -/
def Server.check (s : Server) (kind : String) (auth : Option String) : Except Response Server :=
  match bearer auth with
  | none => .error (s.fail 401 "AuthRequired" "Authentication Required")
  | some t =>
    match parseToken s.cfg t with
    | none => .error (s.fail 400 "InvalidToken" "Token could not be verified")
    | some (k, g) =>
      if k != kind then .error (s.fail 400 "InvalidToken" "Bad token scope")
      else match s.live with
        | none => .error (s.fail 400 "InvalidToken" "Token has been revoked")
        | some l =>
          if kind == "refresh" then
            if g == l.gen then .ok s else .error (s.fail 400 "InvalidToken" "Token has been revoked")
          else if g < l.gen then .error (s.fail 400 "ExpiredToken" "Token has expired")
          else if g > l.gen then .error (s.fail 400 "InvalidToken" "Token could not be verified")
          else if l.expired || l.uses ≥ l.life then
            .error (s.fail 400 "ExpiredToken" "Token has expired")
          else .ok { s with live := some { l with uses := l.uses + 1 } }

def Server.createSession (s : Server) (body : String) : Server × Response :=
  match decode body with
  | some j =>
    match j.str? "identifier", j.str? "password" with
    | some i, some p =>
      if (i == s.cfg.identifier || i == s.cfg.did) && p == s.cfg.password then s.issue
      else (s, s.fail 401 "AuthenticationRequired" "Invalid identifier or password")
    | _, _ => (s, s.fail 400 "InvalidRequest" "Input must have the properties identifier and password")
  | none => (s, s.fail 400 "InvalidRequest" "Request body is not JSON")

/-- `getTimeline`'s answer, once its token is checked. It changes nothing. -/
def Server.getTimeline (s : Server) (params : List (String × String)) : Response :=
  let limit := match params.lookup "limit" with
    | none => some 50
    | some v => (digits 3 v).bind fun n => if 1 ≤ n && n ≤ 100 then some n else none
  match limit with
  | none => s.fail 400 "InvalidRequest" "limit must be an integer from 1 to 100"
  | some n =>
    match params.lookup "cursor" with
    | none => .json 200 [] (page s.cfg s.length n none).toJson s.delayMs
    | some cur =>
      match cursorPos s.cfg s.length cur with
      | some k => .json 200 [] (page s.cfg s.length n (some k)).toJson s.delayMs
      | none => s.fail 400 "InvalidRequest" "Malformed cursor"

/-- An XRPC method, once the request is counted and no fault is due. -/
def Server.xrpc (s : Server) (r : Req) (nsid : String) (params : List (String × String)) :
    Server × Response :=
  let post := r.method == "POST"
  let get := r.method == "GET"
  if nsid == nsidCreateSession then
    if post then s.createSession r.body else (s, s.fail 400 "InvalidRequest" "Incorrect HTTP method")
  else if nsid == nsidRefreshSession then
    if !post then (s, s.fail 400 "InvalidRequest" "Incorrect HTTP method")
    else match s.check "refresh" r.authorization with
      | .ok s => s.issue
      | .error e => (s, e)
  else if nsid == nsidGetSession then
    if !get then (s, s.fail 400 "InvalidRequest" "Incorrect HTTP method")
    else match s.check "access" r.authorization with
      | .ok s => (s, .json 200 [] (.obj s.accountJson) s.delayMs)
      | .error e => (s, e)
  else if nsid == nsidGetTimeline then
    if !get then (s, s.fail 400 "InvalidRequest" "Incorrect HTTP method")
    else match s.check "access" r.authorization with
      | .ok s => (s, s.getTimeline params)
      | .error e => (s, e)
  else (s, s.fail 501 "MethodNotImplemented" "Method Not Implemented")

/-- The reply a fault gives. -/
def Server.faultResponse (s : Server) : Fault → Response
  | .internal => s.fail 500 "InternalServerError" "Internal Server Error"
  | .unavailable => s.fail 503 "ServiceUnavailable" "Service Unavailable"
  | .rateLimit =>
    .json 429 [("ratelimit-limit", "3000"), ("ratelimit-remaining", "0"),
               ("ratelimit-reset", toString (epoch / 1000 + 300 + s.count)),
               ("ratelimit-policy", "3000;w=300")]
      (errJson "RateLimitExceeded" "Rate Limit Exceeded") s.delayMs
  | .timeout => .hang

/-- What the control endpoints change (`/control/<name>`). -/
inductive Control where
  /-- `n` posts arrive at the head. -/
  | post (n : Nat)
  /-- The access token expires now. -/
  | expire
  /-- The session ends on the server: its refresh token is refused too. -/
  | revoke
  /-- The next `n` XRPC calls fail with `f`. -/
  | fail (n : Nat) (f : Fault)
  /-- Every XRPC reply waits `ms` milliseconds (`0`: no delay). -/
  | slow (ms : Nat)
deriving Repr, DecidableEq, Inhabited

def Server.control (s : Server) : Control → Server
  | .post n => { s with length := s.length + n }
  | .expire => { s with live := s.live.map fun l => { l with expired := true } }
  | .revoke => { s with live := none }
  | .fail n f => { s with faults := s.faults ++ List.replicate n f }
  | .slow ms => { s with delayMs := ms }

/-- What `/control/state` answers, and every control endpoint after its change. -/
def Server.stateJson (s : Server) : Json :=
  .obj ([("length", Json.ofNat s.length), ("count", Json.ofNat s.count),
         ("issued", Json.ofNat s.issued)]
    ++ opt "live" (fun (l : Live) => .obj [("gen", Json.ofNat l.gen), ("life", Json.ofNat l.life),
         ("uses", Json.ofNat l.uses), ("expired", .bool l.expired)]) s.live
    ++ [("faults", .arr (s.faults.map fun f => .str (match f with
          | .internal => "500" | .unavailable => "503" | .rateLimit => "429" | .timeout => "timeout"))),
        ("delayMs", Json.ofNat s.delayMs)])

def Control.parse (name : String) (params : List (String × String)) : Option Control :=
  let num (k : String) (d : Nat) : Option Nat := match params.lookup k with
    | none => some d
    | some v => digits 6 v
  match name with
  | "post" => (num "n" 1).map .post
  | "expire" => some .expire
  | "revoke" => some .revoke
  | "fail" => do
    let n ← num "n" 1
    let f ← Fault.ofString ((params.lookup "kind").getD "500")
    some (.fail n f)
  | "slow" => (num "ms" 0).map .slow
  | _ => none

/-- `/img/<w>x<h>/<name>.png`, each side 1 to 4096. -/
def imageSize (path : String) : Option (Nat × Nat) :=
  match path.splitOn "/" with
  | ["", "img", wh, name] =>
    if !name.endsWith ".png" then none
    else match wh.splitOn "x" with
      | [w, h] => do
        let w ← digits 4 w
        let h ← digits 4 h
        if 1 ≤ w && w ≤ 4096 && 1 ≤ h && h ≤ 4096 then some (w, h) else none
      | _ => none
  | _ => none

/-- One request. An XRPC request is counted and the posts due after it arrive; a fault queued
by `Control.fail` answers it instead of the method. Images and control requests aren't
counted. -/
def Server.handle (s : Server) (r : Req) : Server × Response :=
  let (path, params) := splitPath r.path
  if path.startsWith "/xrpc/" then
    let s := { s with length := s.length + arrivals s.cfg s.count, count := s.count + 1 }
    match s.faults with
    | f :: fs => let s := { s with faults := fs }; (s, s.faultResponse f)
    | [] => s.xrpc r (path.drop 6).toString params
  else if path.startsWith "/control/" then
    let name := (path.drop 9).toString
    if name == "state" then
      (s, if r.method == "GET" then .json 200 [] s.stateJson 0
          else .json 400 [] (errJson "InvalidRequest" "Incorrect HTTP method") 0)
    else if r.method != "POST" then (s, .json 400 [] (errJson "InvalidRequest" "Incorrect HTTP method") 0)
    else match Control.parse name params with
      | some c => let s := s.control c; (s, .json 200 [] s.stateJson 0)
      | none => (s, .json 400 [] (errJson "InvalidRequest" "Unknown control or bad parameter") 0)
  else if path.startsWith "/img/" && r.method == "GET" then
    match imageSize path with
    | some (w, h) => (s, .png w h)
    | none => (s, .json 404 [] (errJson "NotFound" "Not Found") 0)
  else (s, .json 404 [] (errJson "NotFound" "Not Found") 0)

/-! ## The host: Keychain and capture

cairn#205's rules (cairn's docs/effects.md, "Secrets in the Keychain"): a request whose secret
item is missing answers `failed notFound` and isn't sent; `capture` applies to a 2xx JSON object
reply, each listed top-level member there exactly once and a string, all or nothing (else
`failed invalid`), the value written to its item and blanked in the body Lean receives. -/

def jsonType : String := "application/json; charset=utf-8"

/-- Capture `fields` from a body: the items written and the body with them blanked. -/
def captureBody (fields : List (String × String)) : Json → Option (List (String × String) × Json)
  | .obj kvs =>
    let got := fields.map fun (f, acct) =>
      match kvs.filter (·.1 == f) with
      | [(_, .str v)] => some (acct, v)
      | _ => none
    (optMap id got).map fun items =>
      (items, .obj (kvs.map fun (k, v) => if fields.any (·.1 == k) then (k, .str "") else (k, v)))
  | _ => none

/-- The reply Lean receives for a response, and the items the host writes. -/
def hostReply (capture : List (String × String)) : Response → List (String × String) × Cairn.Reply
  | .hang => ([], .failed .timeout "The request timed out.")
  | .png _ _ => ([], .http 200 [("content-type", "image/png")] ByteArray.empty)
  | .json st hs body _ =>
    let hs := ("content-type", jsonType) :: hs
    if capture.isEmpty || !isSuccess st then ([], .http st hs (encode body).toUTF8)
    else match captureBody capture body with
      | some (items, b) => (items, .http st hs (encode b).toUTF8)
      | none => ([], .failed .invalid "capture: a field is missing, repeated or not a string")

/-- The path and query of a URL: what follows `scheme://host`. -/
def pathOf (url : String) : String :=
  match splitFirst url "://" with
  | (_, some rest) => match splitFirst rest "/" with
    | (_, some p) => "/" ++ p
    | (_, none) => "/"
  | (p, none) => p

/-- The server and the host in front of it, as the session machine sees them. -/
structure World where
  server : Server
  /-- The Keychain: each item's value (a token from `server`, so a marker). -/
  items : List (String × String) := []
  /-- Whether the host captures. Only `false` to check that a leak is caught. -/
  captures : Bool := true
deriving Repr, Inhabited

def World.init (c : Config) : World := { server := Server.init c }

def World.forget (w : World) (item : String) : World :=
  { w with items := w.items.filter (·.1 != item) }

def World.put (w : World) (kv : String × String) : World :=
  { w with items := kv :: w.items.filter (·.1 != kv.1) }

/-- Which generation item `item` holds, if any. -/
def World.generation (w : World) (item : String) : Option Nat :=
  (w.items.lookup item).bind fun t => (parseToken w.server.cfg t).map (·.2)

/-- The host sends `r` (an `http` request; anything else is `failed invalid`) and hands Lean the
reply. With `lose`, the server handles the request but its reply never comes back (`failed
timeout`): a rotation the host never captures. -/
def World.send (w : World) (r : Cairn.Request) (lose : Bool := false) : World × Cairn.Reply :=
  match r with
  | .http method url _ body _ secret capture _ =>
    let auth : Except Cairn.Reply (Option String) := match secret with
      | none => .ok none
      | some sec => match sec.source with
        | .keychain a => match w.items.lookup a with
          | none => .error (.failed .notFound s!"No Keychain item {a}.")
          | some v => .ok (some (sec.scheme ++ v))
        | .env .. => .error (.failed .notFound "No environment secret.")
    match auth with
    | .error rep => (w, rep)
    | .ok auth =>
      let (srv, resp) := w.server.handle
        { method, path := pathOf url, authorization := auth,
          body := (String.fromUTF8? body).getD "" }
      let w := { w with server := srv }
      if lose then (w, .failed .timeout "The request timed out.")
      else
        let (items, reply) := hostReply (if w.captures then capture else []) resp
        (items.foldl World.put w, reply)
  | _ => (w, .failed .invalid "not an http request")

/-! ## Markers -/

/-- Every token holds this; no Lean value should. -/
def hasMarker (s : String) : Bool := s.contains tokenPrefix

def bytesHaveMarker (b : ByteArray) : Bool :=
  let m := tokenPrefix.toUTF8.toList
  let rec go : List UInt8 → Bool
    | [] => m.isEmpty
    | x :: xs => m.isPrefixOf (x :: xs) || go xs
  go b.toList

/-- Whether a reply Lean receives holds a token. -/
def replyHasMarker : Cairn.Reply → Bool
  | .http _ hs b => hs.any (fun (k, v) => hasMarker k || hasMarker v) || bytesHaveMarker b
  | .failed _ m => hasMarker m
  | .bytes b => bytesHaveMarker b
  | .names ns => ns.any hasMarker
  | .app _ n => hasMarker n
  | _ => false

/-! ## For `cairn fuzz`

`replies` plugs into `Cairn.Fuzz.Custom.replies`. Cairn's hook keeps no state between replies,
so each reply is what `Server.handle` answers in a state drawn at random that fits the request:

* the timeline as it stands at request `id`: `base` posts and those that arrived before it
  (`arrivedBefore`), so it grows at the head as ids grow and a cursor always means the same posts;
* the session at generation 1 (a stale refresh token is generation 0); the access token expired
  with chance `1/life`; a refresh refused one time in ten;
* the Keychain from the session's phase (`Hooks.phase`): items held while signed in or
  refreshing, maybe at launch, not when signed out; a missing item answers `failed notFound`;
* a fault one time in eight (500, 503, 429, a timeout or a network failure);
* the token the request names: its `secret`'s Keychain item (`access` or `refresh`), none
  without one;
* capture as the request asks (`Request.http`'s `capture`, cairn#205), unless `Hooks.capture`
  says otherwise: tokens are markers, so a reply whose request didn't capture them hands Lean a
  marker.

Image URLs on the fake (`/img/<w>x<h>/…`) are answered with their size. -/

/-- The NSID of an XRPC URL. -/
def nsidOf (url : String) : String :=
  match splitFirst (splitFirst (pathOf url) "?").1 "/xrpc/" with
  | (_, some n) => n
  | _ => ""

/-- The origin of a URL: everything before its path. -/
def originOf (url : String) : String :=
  match splitFirst url "://" with
  | (scheme, some rest) => scheme ++ "://" ++ (splitFirst rest "/").1
  | (u, none) => u

structure Hooks (S : Type) where
  /-- The session's phase in the app's state, for which Keychain items the host holds. -/
  phase : S → Option Session.Phase := fun _ => none
  /-- The fields the host captures for request `id`: by default what the request asks
  (`captureOf`). Only a check that a leak is caught (capture off) changes it. -/
  capture : S → Nat → Cairn.Request → List (String × String) := fun _ _ r => captureOf r

/-- Whether the host holds the session's items in this phase (`none`: maybe). -/
def held : Option Session.Phase → Option Bool
  | some (.signedIn _) | some (.refreshing ..) | none => some true
  | some .launched => none
  | some .signedOut | some (.signingIn ..) => some false

def faultReply (c : Config) (id : Nat) : Gen Cairn.Reply := do
  let s : Server := { Server.init c with count := id }
  match ← Gen.below 5 with
  | 0 => return (hostReply [] (s.faultResponse .internal)).2
  | 1 => return (hostReply [] (s.faultResponse .unavailable)).2
  | 2 => return (hostReply [] (s.faultResponse .rateLimit)).2
  | 3 => return .failed .timeout "The request timed out."
  | _ => return .failed .network "The network connection was lost."

/-- A `Cairn.Fuzz.Custom.replies` generator for the fake. -/
def replies {S : Type} (cfg : Config) (hooks : Hooks S := {}) :
    S → Nat → Cairn.Request → Option (Gen Cairn.Reply)
  | _, _, .loadImage src _ =>
    if (pathOf src).startsWith "/img/" then
      (imageSize (splitFirst (pathOf src) "?").1).map fun (w, h) => pure (.image w h)
    else none
  | st, id, r@(.http method url _ body ..) => some do
    let c := { cfg with service := originOf url }
    if ← Gen.chance 1 8 then return ← faultReply c id
    let item := itemOf r
    let kind := if item == some refreshItem then "refresh" else "access"
    let authed := item.isSome
    let maybe ← Gen.bool
    let holds := (held (hooks.phase st)).getD maybe
    if authed && !holds then return .failed .notFound s!"No Keychain item {kind}."
    let expired ← Gen.chance 1 (max cfg.life 1)
    let stale ← Gen.chance 1 10
    let s : Server := { cfg := c, length := c.base + arrivedBefore c id, count := id, issued := 1,
                        live := some { gen := 1, life := c.lifeOf 1, uses := if expired then c.lifeOf 1 else 0 } }
    let gen := if kind == "refresh" && stale then 0 else 1
    let auth := if authed then some ("Bearer " ++ token c kind gen) else none
    let req : Req := { method, path := pathOf url, authorization := auth,
                       body := (String.fromUTF8? body).getD "" }
    return (hostReply (hooks.capture st id r) (s.handle req).2).2
  | _, _, _ => none

end CairnAtproto.Fake
