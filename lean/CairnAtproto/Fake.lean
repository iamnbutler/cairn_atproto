module

public import CairnAtproto.Session
public import Cairn.Fuzz.Rng
public import CairnAtproto.Datetime
public import CairnAtproto.Acts

/-! # A fake PDS

A model of the part of a Bluesky PDS that M4 talks to, so nothing needs the network to be
tested (cairn#208). The same behaviour runs over HTTP in `tools/fake-pds/` (Bun), and
`tools/fake-pds/replay.ts` checks that the two agree request by request.

* **The timeline** only grows at its head. Post `k` (from the oldest, `0`) is a pure function of
  the seed and `k` (`postAt`), so a post never changes once it is there, and between requests new
  ones arrive at the head at random (`arrivals`), or when asked (`Control.post`). Some posts are
  replies, to an older post or to a deleted or blocked one (`replyTarget`, cairn#236).
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
* **As a `cairn fuzz` server** (`server`, cairn#260): a `Cairn.Fuzz.Server` whose world is a
  whole `World`, drawn per sequence (`worldGen`), so writes, likes and mutes persist through it.

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
  /-- After each XRPC request another account acts with chance `1/act` (`0`: never). -/
  act : Nat := 4
  /-- The AppView sees a change 0 to `lag` requests after it (`Server.lag`, which
  `/control/lag` changes, starts here). -/
  lag : Nat := 2
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

/-- UTC milliseconds since the epoch as `YYYY-MM-DDTHH:MM:SS.mmmZ` (`formatDatetime`). -/
def iso (ms : Nat) : String := formatDatetime ms

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

/-- The tester's own profile, as views show it. -/
def Config.me (c : Config) : Profile :=
  { did := c.did, handle := c.identifier, displayName := some "Tester",
    avatar := some (imgUrl c 96 96 "avatar-tester") }

def authorOf (c : Config) (k : Nat) : Nat := pick c.seed 1 k authorNames.length
/-- About one post in four (never post `0`) is the tester's own. -/
def isMine (c : Config) (k : Nat) : Bool := k != 0 && pick c.seed 22 k 4 == 0
/-- Who wrote post `k`: the tester, or one of the other accounts. -/
def poster (c : Config) (k : Nat) : Profile := if isMine c k then c.me else author c (authorOf c k)
def createdMs (c : Config) (k : Nat) : Nat := epoch + k * 60000 + pick c.seed 5 k 59000
def rkey (k : Nat) : String := "3fk" ++ padLeft 8 '0' (toString k)
def postUri (c : Config) (k : Nat) : String :=
  s!"at://{(poster c k).did}/app.bsky.feed.post/{rkey k}"
def postCid (c : Config) (k : Nat) : String := "bafyreifake" ++ hex16 (hash c.seed 2 k)

def textOf (c : Config) (k : Nat) : String :=
  s!"#{k} " ++ " ".intercalate ((List.range (1 + pick c.seed 3 k 12)).map fun j =>
    words.getD (pick c.seed 4 (k * 16 + j) words.length) "")

/-- One post in ten by another account mentions the tester. -/
def mentions (c : Config) (k : Nat) : Bool := !isMine c k && pick c.seed 24 k 10 == 0

/-- Post `k`'s text: words, and the tester's handle when it mentions them. -/
def postText (c : Config) (k : Nat) : String :=
  textOf c k ++ (if mentions c k then s!" @{c.identifier}" else "")

/-- The older post that post `k` quotes, if it is a quote (one in eight, never post `0`). -/
def quotesOf (c : Config) (k : Nat) : Option Nat :=
  if k != 0 && pick c.seed 10 k 8 == 3 then some (pick c.seed 23 k k) else none

/-- Post `j` as a quote shows it. -/
def quoted (c : Config) (j : Nat) : QuotedPost :=
  { uri := postUri c j, cid := postCid c j, author := poster c j, text := postText c j,
    createdAt := iso (createdMs c j), indexedAt := iso (createdMs c j) }

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
  | _ => (quotesOf c k).map fun j => .record (.post (quoted c j))

/-! ### Replies (cairn#236)

One post in four (never post `0`) is a reply. Its parent is an older post `j < k` (six times in
eight), a deleted post (`notFoundPost`) or a post by an account that blocks the tester
(`blockedPost`). Its thread's root is found by following parents down: the oldest post of the
chain, or the deleted or blocked post the chain reaches. The post's record carries `reply`
(root and parent by URI and CID); its feed item carries the views (`ReplyCtx`), with the
grandparent's author when the parent is itself a reply to a post. -/

/-- What a reply's parent (or root) is. -/
inductive Parent where
  /-- Post `j` of the timeline. -/
  | post (j : Nat)
  /-- A deleted post. -/
  | notFound
  /-- A post by an account that blocks the tester. -/
  | blocked
deriving Repr, DecidableEq, Inhabited

/-- What post `k` replies to, if it is a reply. -/
def replyTarget (c : Config) (k : Nat) : Option Parent :=
  if k = 0 then none
  else if pick c.seed 16 k 4 = 0 then
    match pick c.seed 18 k 8 with
    | 0 => some .notFound
    | 1 => some .blocked
    | _ => some (.post (pick c.seed 17 k k))
  else none

/-- The root of the thread post `j` is in, following parents down at most `fuel` steps (parents
are older, so `j` steps reach it). -/
def rootFrom (c : Config) : Nat → Nat → Parent
  | 0, j => .post j
  | n + 1, j =>
    match replyTarget c j with
    | some (.post i) => rootFrom c n i
    | some p => p
    | none => .post j

/-- The root of post `k`'s thread, when it is a reply. -/
def threadRoot (c : Config) (k : Nat) : Parent :=
  match replyTarget c k with
  | some (.post j) => rootFrom c j j
  | some p => p
  | none => .post k

def goneUri (k : Nat) : String := s!"at://did:plc:fakeauthorgone/app.bsky.feed.post/3fkgone{padLeft 8 '0' (toString k)}"
def goneCid (c : Config) (k : Nat) : String := "bafyreigone" ++ hex16 (hash c.seed 19 k)
def blockedUri (k : Nat) : String := s!"at://did:plc:fakeauthorblocker/app.bsky.feed.post/3fkblock{padLeft 8 '0' (toString k)}"
def blockedCid (c : Config) (k : Nat) : String := "bafyreiblock" ++ hex16 (hash c.seed 21 k)

/-- A parent (or root) of post `k`, by URI and CID, as a record's `reply` names it. -/
def parentRef (c : Config) (k : Nat) : Parent → StrongRef
  | .post j => ⟨postUri c j, postCid c j⟩
  | .notFound => ⟨goneUri k, goneCid c k⟩
  | .blocked => ⟨blockedUri k, blockedCid c k⟩

/-- Post `k`'s seeded like and repost counts: other accounts' before the fake started. -/
def seededLikes (c : Config) (k : Nat) : Nat := pick c.seed 8 k 100
def seededReposts (c : Config) (k : Nat) : Nat := pick c.seed 7 k 20

/-- Post `k`'s view, with its record's `reply` when it is one: a function of the seed and `k`. -/
def postView (c : Config) (k : Nat) : Post :=
  let at_ := iso (createdMs c k)
  { uri := postUri c k, cid := postCid c k, author := poster c k,
    text := postText c k, createdAt := at_, embed := embedOf c k,
    replyCount := pick c.seed 6 k 5, repostCount := seededReposts c k,
    likeCount := seededLikes c k, quoteCount := pick c.seed 9 k 3, indexedAt := at_,
    reply := (replyTarget c k).map fun p =>
      { root := parentRef c k (threadRoot c k), parent := parentRef c k p } }

/-- A parent or root as a feed item's reply context shows it. -/
def parentView (c : Config) (k : Nat) : Parent → ReplyRef
  | .post j => .post (postView c j)
  | .notFound => .notFound (goneUri k)
  | .blocked => .blocked (blockedUri k)

/-- Post `k`'s reply context: the views of its root and parent, and the grandparent's author. -/
def replyCtx (c : Config) (k : Nat) : Option ReplyCtx :=
  (replyTarget c k).map fun p =>
    { root := parentView c k (threadRoot c k), parent := parentView c k p,
      grandparentAuthor := match p with
        | .post j => match replyTarget c j with
          | some (.post i) => some (poster c i)
          | _ => none
        | _ => none }

/-- Who reposted post `k` into the timeline, if it is there as a repost (one in eight). -/
def reposter (c : Config) (k : Nat) : Option Nat :=
  if pick c.seed 14 k 8 = 0 then some (pick c.seed 15 k authorNames.length) else none

/-- Post `k`, counted from the oldest: a function of the seed and `k` only. -/
def postAt (c : Config) (k : Nat) : FeedItem :=
  let at_ := iso (createdMs c k)
  { post := postView c k, reply := replyCtx c k,
    reason := (reposter c k).map fun i => .repost (author c i) at_ }

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

/-- The posts below `hi` that `keep` keeps, newest first. -/
def keptBelow (keep : Nat → Bool) (hi : Nat) : List Nat := ((List.range hi).reverse).filter keep

/-- A page of the posts `keep` keeps (the timeline leaves out muted accounts): `limit` of those
older than post `before` (the head when `none`), newest first, and the cursor of its oldest post
when more are kept below it. -/
def pageWhere (c : Config) (keep : Nat → Bool) (length limit : Nat) (before : Option Nat) :
    List Nat × Option String :=
  let ks := keptBelow keep (before.getD length)
  let taken := ks.take limit
  (taken, if limit < ks.length then taken.getLast?.map (cursorOf c) else none)

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
  /-- 400 `InvalidRequest`: the call is refused, and not applied. -/
  | refused
  /-- The server applies the call, but its reply is lost: the client times out. -/
  | lostAfter
deriving Repr, DecidableEq, Inhabited

def Fault.ofString : String → Option Fault
  | "500" => some .internal
  | "503" => some .unavailable
  | "429" => some .rateLimit
  | "timeout" => some .timeout
  | "400" => some .refused
  | "lost-after" => some .lostAfter
  | _ => none

def Fault.toString : Fault → String
  | .internal => "500"
  | .unavailable => "503"
  | .rateLimit => "429"
  | .timeout => "timeout"
  | .refused => "400"
  | .lostAfter => "lost-after"

/-- The session the server holds: its token generation, how many calls its access token serves
and has served, and whether it was expired by hand. -/
structure Live where
  gen : Nat
  life : Nat
  uses : Nat := 0
  expired : Bool := false
deriving Repr, DecidableEq, Inhabited

/-! ## What the server holds (cairn#251)

Everything that changes is a `Change`, appended to the server's log (`Server.log`) as an `Entry`
with the request count from which the AppView sees it (`vis`) and when it was indexed (`ms`):

* the tester's writes: a record put or deleted in their repo, an account muted or unmuted;
* another account acting: a like or repost of a post, a follow of the tester, or undoing one
  (`Act`), between requests at a seeded rate or on `POST /control/act`;
* a post arriving that replies to, quotes or mentions the tester (`notice`).

`Facts` is what a run of the log adds up to. The server keeps the whole log's (`Server.now`): the
tester's PDS answers `getRecord` from it at once. The AppView's views (timeline, `getPosts`,
`getProfile`, notifications) add up only the entries it has indexed (`Server.seen`), each `0` to
`lag` requests after it was made. An entry is never seen before the one before it (`vis` never
decreases along the log), so a view is a prefix of the log: one moment, its counts and viewer
state together. -/

/-- What another account does. -/
inductive ActKind where
  | like
  | repost
  | follow
deriving Repr, DecidableEq, Inhabited

def ActKind.ofIndex : Nat → ActKind
  | 0 => .like
  | 1 => .repost
  | _ => .follow

def ActKind.ofString : String → Option ActKind
  | "like" => some .like
  | "repost" => some .repost
  | "follow" => some .follow
  | _ => none

def ActKind.collection : ActKind → String
  | .like => nsidLike
  | .repost => nsidRepost
  | .follow => nsidFollow

def ActKind.reason : ActKind → NotificationReason
  | .like => .like
  | .repost => .repost
  | .follow => .follow

/-- Another account (`authorNames` index `actor`) likes or reposts post `post`, or follows the
tester (`post` is `0`); `undo` takes back the one it made before. -/
structure Act where
  kind : ActKind
  actor : Nat
  post : Nat := 0
  undo : Bool := false
deriving Repr, DecidableEq, Inhabited

inductive Change where
  /-- The tester writes `record` at `collection/rkey` in their repo; its CID is `cid`. -/
  | put (collection rkey : String) (record : Record) (cid : String)
  | delete (collection rkey : String)
  | mute (did : String)
  | unmute (did : String)
  | act (a : Act)
  /-- Post `k` arrived; it replies to, quotes or mentions the tester. -/
  | post (k : Nat)
deriving Repr, DecidableEq, Inhabited

structure Entry where
  change : Change
  /-- Its place in the log, from `0`. -/
  seq : Nat
  /-- The AppView sees it in requests counted from `vis` on. -/
  vis : Nat
  /-- When it was indexed, in milliseconds: strictly increasing along the log. -/
  ms : Nat
deriving Repr, DecidableEq, Inhabited

/-- A record in the tester's repo. -/
structure Rec where
  collection : String
  rkey : String
  record : Record
  cid : String
deriving Repr, DecidableEq, Inhabited

/-- What a run of the log adds up to. -/
structure Facts where
  /-- The tester's records, the latest written first. -/
  repo : List Rec := []
  /-- The accounts the tester muted (DIDs), the latest first. -/
  muted : List String := []
  /-- Other accounts' likes and reposts: the account's index and the post's URI. -/
  likes : List (Nat × String) := []
  reposts : List (Nat × String) := []
  /-- The other accounts that follow the tester. -/
  follows : List Nat := []
deriving Repr, DecidableEq, Inhabited

def Facts.find (f : Facts) (collection rkey : String) : Option Rec :=
  f.repo.find? fun r => r.collection == collection && r.rkey == rkey

def Facts.without (f : Facts) (collection rkey : String) : List Rec :=
  f.repo.filter fun r => !(r.collection == collection && r.rkey == rkey)

/-- One change's effect. -/
def Facts.apply (c : Config) (f : Facts) : Change → Facts
  | .put col k r cid => { f with repo := ⟨col, k, r, cid⟩ :: f.without col k }
  | .delete col k => { f with repo := f.without col k }
  | .mute d => { f with muted := d :: f.muted.filter (· != d) }
  | .unmute d => { f with muted := f.muted.filter (· != d) }
  | .act a =>
    let u := postUri c a.post
    match a.kind with
    | .like => { f with likes := if a.undo then f.likes.filter (· != (a.actor, u)) else (a.actor, u) :: f.likes }
    | .repost => { f with reposts := if a.undo then f.reposts.filter (· != (a.actor, u)) else (a.actor, u) :: f.reposts }
    | .follow => { f with follows := if a.undo then f.follows.filter (· != a.actor) else a.actor :: f.follows }
  | .post _ => f

/-- What a run of entries adds up to. -/
def Facts.ofLog (c : Config) (es : List Entry) : Facts := es.foldl (fun f e => f.apply c e.change) {}

/-- The URI of a record in the tester's repo. -/
def recUri (c : Config) (r : Rec) : String := s!"at://{c.did}/{r.collection}/{r.rkey}"

/-- The tester's like records of the post at `uri`. -/
def Facts.myLikes (f : Facts) (uri : String) : List Rec :=
  f.repo.filter fun r => match r.record with | .like s _ => s.uri == uri | _ => false

def Facts.myReposts (f : Facts) (uri : String) : List Rec :=
  f.repo.filter fun r => match r.record with | .repost s _ => s.uri == uri | _ => false

/-- The tester's follow record of the account `did`, if any. -/
def Facts.myFollow (f : Facts) (did : String) : Option Rec :=
  f.repo.find? fun r => match r.record with | .follow d _ => d == did | _ => false

/-- The like records of the post at `uri`: other accounts' and the tester's. -/
def Facts.likeCount (f : Facts) (uri : String) : Nat :=
  (f.likes.filter (·.2 == uri)).length + (f.myLikes uri).length

def Facts.repostCount (f : Facts) (uri : String) : Nat :=
  (f.reposts.filter (·.2 == uri)).length + (f.myReposts uri).length

/-! ### Views, as the AppView shows them from a run of the log -/

/-- A profile with the tester's state toward it: muted, followed (the follow record's URI). -/
def viewProfile (c : Config) (f : Facts) (p : Profile) : Profile :=
  if p.did == c.did then p
  else { p with viewer := { muted := f.muted.contains p.did,
                            following := (f.myFollow p.did).map (recUri c) } }

def viewEmbed (c : Config) (f : Facts) : Embed → Embed
  | .record (.post q) => .record (.post { q with author := viewProfile c f q.author })
  | e => e

/-- A post with its counts and the tester's like and repost of it, all from `f`: a count is the
seeded one (accounts outside the fake) plus the like (repost) records in `f`, the tester's
included, and `viewer.like` is the tester's latest like record of it. -/
def viewPost (c : Config) (f : Facts) (p : Post) : Post :=
  { p with author := viewProfile c f p.author, embed := p.embed.map (viewEmbed c f),
           likeCount := p.likeCount + f.likeCount p.uri,
           repostCount := p.repostCount + f.repostCount p.uri,
           viewer := { like := (f.myLikes p.uri).head?.map (recUri c),
                       repost := (f.myReposts p.uri).head?.map (recUri c) } }

def viewRef (c : Config) (f : Facts) : ReplyRef → ReplyRef
  | .post p => .post (viewPost c f p)
  | r => r

def viewReason (c : Config) (f : Facts) : Reason → Reason
  | .repost b t => .repost (viewProfile c f b) t
  | r => r

def viewItem (c : Config) (f : Facts) (i : FeedItem) : FeedItem :=
  { post := viewPost c f i.post,
    reply := i.reply.map fun r => { root := viewRef c f r.root, parent := viewRef c f r.parent,
                                    grandparentAuthor := r.grandparentAuthor.map (viewProfile c f) },
    reason := i.reason.map (viewReason c f) }

/-- Whether the timeline shows post `k`: not by a muted account, nor reposted by one. -/
def shown (c : Config) (f : Facts) (k : Nat) : Bool :=
  !f.muted.contains (poster c k).did &&
    match reposter c k with
    | some i => !f.muted.contains (author c i).did
    | none => true

/-! ### Notifications -/

/-- What post `k` (by another account) does to the tester: a reply to their post, a quote of it,
or a mention; with the post acted on. -/
def notice (c : Config) (k : Nat) : Option (NotificationReason × Option String) :=
  let replyTo := match replyTarget c k with
    | some (.post j) => if isMine c j then some j else none
    | _ => none
  let quoteOf := match quotesOf c k with
    | some j => if isMine c j then some j else none
    | none => none
  if isMine c k then none
  else match replyTo, quoteOf with
    | some j, _ => some (.reply, some (postUri c j))
    | none, some j => some (.quote, some (postUri c j))
    | none, none => if mentions c k then some (.mention, none) else none

/-- The record key of another account's like, repost or follow made in log entry `seq`. -/
def actRkey (seq : Nat) : String := "3fa" ++ padLeft 10 '0' (toString seq)

/-- The notification a log entry gives the tester, if any, as `f` shows its author, read when
`seenAt` is at or past it. -/
def noticeOf (c : Config) (f : Facts) (seenAt : Option Nat) (e : Entry) : Option Notification :=
  let isRead := match seenAt with | some t => decide (e.ms ≤ t) | none => false
  let at_ := iso e.ms
  match e.change with
  | .post k => (notice c k).map fun (r, subj) =>
      { uri := postUri c k, cid := postCid c k, author := viewProfile c f (poster c k), reason := r,
        reasonSubject := subj, text := some (postText c k), isRead, indexedAt := at_ }
  | .act a =>
    if a.undo || (a.kind != .follow && !isMine c a.post) then none
    else
      let who := author c a.actor
      some { uri := s!"at://{who.did}/{a.kind.collection}/{actRkey e.seq}",
             cid := "bafyreiact" ++ hex16 (hash c.seed 38 e.seq),
             author := viewProfile c f who, reason := a.kind.reason,
             reasonSubject := if a.kind == .follow then none else some (postUri c a.post),
             isRead, indexedAt := at_ }
  | _ => none

/-- A page of a list kept oldest first (`xs`), as a cursor pages it: `limit` items below position
`before` (all of them when `none`), newest first, and the position of the oldest unless it is
the first. -/
def runPage {α : Type} (xs : List α) (limit : Nat) (before : Option Nat) : List α × Option Nat :=
  let hi := before.getD xs.length
  let lo := hi - min limit hi
  (((xs.take hi).drop lo).reverse, if lo = 0 then none else some lo)

/-! ## The server -/

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
  /-- Every change, oldest first. -/
  log : List Entry := []
  /-- What the whole log adds up to (`Facts.ofLog cfg log`): what the tester's PDS holds. -/
  now : Facts := {}
  /-- The AppView sees a change 0 to `lag` requests after it. -/
  lag : Nat := 0
  /-- The last entry's `vis` and `ms`. -/
  lastVis : Nat := 0
  lastMs : Nat := epoch
  /-- `updateSeen`'s time, in milliseconds. -/
  seenAt : Option Nat := none
deriving Repr, Inhabited

/-- Append a change to the log. The AppView sees it `0` to `lag` requests from now (seeded by its
place in the log; at once with `delay := false`), and never before the entry before it. -/
def Server.append (s : Server) (ch : Change) (delay : Bool := true) : Server :=
  let seq := s.log.length
  let d := if delay then pick s.cfg.seed 36 seq (s.lag + 1) else 0
  let vis := max s.lastVis (s.count + d)
  let ms := max (s.lastMs + 1) (match ch with | .post k => createdMs s.cfg k | _ => s.lastMs + 1000)
  { s with log := s.log ++ [⟨ch, seq, vis, ms⟩], now := s.now.apply s.cfg ch, lastVis := vis,
           lastMs := ms }

/-- The log entries for posts `from` to `length - 1` that notify the tester. -/
def Server.noticePosts (s : Server) (from_ : Nat) (delay : Bool := true) : Server :=
  (List.range' from_ (s.length - from_)).foldl
    (fun s k => if (notice s.cfg k).isSome then s.append (.post k) delay else s) s

def Server.init (c : Config) : Server :=
  ({ cfg := c, length := c.base, lag := c.lag } : Server).noticePosts 0 false

/-- The log the AppView has indexed by now. -/
def Server.seenLog (s : Server) : List Entry := s.log.takeWhile (·.vis ≤ s.count)

/-- What the AppView shows now. -/
def Server.seen (s : Server) : Facts := Facts.ofLog s.cfg s.seenLog

/-- The notifications the AppView shows now, oldest first. -/
def Server.notices (s : Server) : List Notification :=
  let f := s.seen
  s.seenLog.filterMap (noticeOf s.cfg f s.seenAt)

/-- Another account acts: likes (or reposts) post `k`, or follows the tester; or takes back the
like, repost or follow it made before. Nothing when post `k` isn't there. -/
def Server.act (s : Server) (kind : ActKind) (actor k : Nat) : Server :=
  if kind != .follow && k ≥ s.length then s
  else
    let undo := match kind with
      | .like => s.now.likes.contains (actor, postUri s.cfg k)
      | .repost => s.now.reposts.contains (actor, postUri s.cfg k)
      | .follow => s.now.follows.contains actor
    s.append (.act { kind, actor, post := if kind == .follow then 0 else k, undo })

/-- The other accounts' act after XRPC request `n`, with chance `1/act`. -/
def Server.othersAct (s : Server) (n : Nat) : Server :=
  if s.cfg.act = 0 then s
  else if pick s.cfg.seed 32 n s.cfg.act != 0 then s
  else s.act (ActKind.ofIndex (pick s.cfg.seed 33 n 3)) (pick s.cfg.seed 34 n authorNames.length)
         (pick s.cfg.seed 35 n (max s.length 1))

/-- The newest of the tester's posts, if any. -/
def Server.newestMine (s : Server) : Option Nat := (List.range s.length).reverse.find? (isMine s.cfg)

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

def Server.ok (s : Server) (body : Json) : Response := .json 200 [] body s.delayMs

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

/-- A `limit` parameter: 1 to 100, 50 when absent. -/
def limitOf (params : List (String × String)) : Option Nat :=
  match params.lookup "limit" with
  | none => some 50
  | some v => (digits 3 v).bind fun n => if 1 ≤ n && n ≤ 100 then some n else none

/-- `getTimeline`'s answer, once its token is checked. It changes nothing. The AppView leaves
out posts by accounts the tester muted, and reposts by them. -/
def Server.getTimeline (s : Server) (params : List (String × String)) : Response :=
  match limitOf params with
  | none => s.fail 400 "InvalidRequest" "limit must be an integer from 1 to 100"
  | some n =>
    let f := s.seen
    let answer (before : Option Nat) : Response :=
      let (ks, cursor) := pageWhere s.cfg (shown s.cfg f) s.length n before
      s.ok ({ feed := ks.map fun k => viewItem s.cfg f (postAt s.cfg k), cursor } : FeedPage).toJson
    match params.lookup "cursor" with
    | none => answer none
    | some cur =>
      match cursorPos s.cfg s.length cur with
      | some k => answer (some k)
      | none => s.fail 400 "InvalidRequest" "Malformed cursor"

/-! ### The tester's repo -/

/-- Whether `repo` names the tester (DID or handle). -/
def Server.isMe (s : Server) (repo : String) : Bool := repo == s.cfg.did || repo == s.cfg.identifier

/-- A record key: 1 to 512 of `A-Z a-z 0-9 . - _ : ~`, and not `.` or `..`. -/
def validRkey (k : String) : Bool :=
  !k.isEmpty && k.length ≤ 512 && k != "." && k != ".." &&
    k.all fun ch => ch.isAlphanum || ch == '.' || ch == '-' || ch == '_' || ch == ':' || ch == '~'

def Server.recJson (s : Server) (r : Rec) : Json :=
  .obj [("uri", .str (recUri s.cfg r)), ("cid", .str r.cid)]

/-- The records the fake takes: likes, reposts, follows. -/
def takes : Record → Bool
  | .other _ => false
  | _ => true

/-- Write `r` at `col/rkey`, with a new CID. -/
def Server.writeRec (s : Server) (col rkey : String) (r : Record) : Server × Response :=
  let cid := "bafyreirec" ++ hex16 (hash s.cfg.seed 37 s.log.length)
  (s.append (.put col rkey r cid), s.ok (s.recJson ⟨col, rkey, r, cid⟩))

/-- `putRecord` of a write, read from its body: write it, unless the same record is already
there (then nothing changes and the answer is the same). -/
def Server.putRec (s : Server) (w : PutRecord) : Server × Response :=
  if !s.isMe w.repo then (s, s.fail 400 "InvalidRequest" "Could not find repo")
  else if !validRkey w.rkey then (s, s.fail 400 "InvalidRequest" "Invalid record key")
  else if !takes w.record then (s, s.fail 400 "InvalidRequest" "Unsupported collection")
  else match s.now.find w.record.collection w.rkey with
    | some old =>
      if old.record = w.record then (s, s.ok (s.recJson old))
      else s.writeRec w.record.collection w.rkey w.record
    | none => s.writeRec w.record.collection w.rkey w.record

/-- `deleteRecord`: delete it if it is there; either way 200. -/
def Server.deleteRec (s : Server) (u : AtUri) : Server × Response :=
  if !s.isMe u.repo then (s, s.fail 400 "InvalidRequest" "Could not find repo")
  else match s.now.find u.collection u.rkey with
    | some _ => (s.append (.delete u.collection u.rkey), s.ok (.obj []))
    | none => (s, s.ok (.obj []))

/-- `getRecord`, from what the PDS holds now (not the AppView's lagging view). -/
def Server.getRec (s : Server) (u : AtUri) : Response :=
  let missing := s.fail 400 "RecordNotFound" s!"Could not locate record: at://{u.repo}/{u.collection}/{u.rkey}"
  if !s.isMe u.repo then missing
  else match s.now.find u.collection u.rkey with
    | some r => s.ok ({ uri := recUri s.cfg r, cid := some r.cid, value := r.record } : RecordView).toJson
    | none => missing

/-! ### Accounts: profiles and mutes -/

/-- The account `actor` names (DID or handle): the tester (`none`) or another (`some i`). -/
def Server.resolve (s : Server) (actor : String) : Option (Option Nat) :=
  if s.isMe actor then some none
  else ((List.range authorNames.length).find? fun i =>
      (author s.cfg i).did == actor || (author s.cfg i).handle == actor).map some

def Server.getProfile (s : Server) (params : List (String × String)) : Response :=
  match (params.lookup "actor").bind s.resolve with
  | none => s.fail 400 "InvalidRequest" "Profile not found"
  | some who =>
    let f := s.seen
    let posts (p : Nat → Bool) := ((List.range s.length).filter p).length
    let d : ProfileDetail := match who with
      | none =>
        { profile := s.cfg.me, description := some "The tester's account on the fake PDS.",
          followersCount := f.follows.length,
          followsCount := (f.repo.filter fun r => r.collection == nsidFollow).length,
          postsCount := posts (isMine s.cfg) }
      | some i =>
        let a := author s.cfg i
        { profile := viewProfile s.cfg f a, description := some s!"{a.handle} on the fake PDS.",
          followersCount := pick s.cfg.seed 25 i 1000 + (if (f.myFollow a.did).isSome then 1 else 0),
          followsCount := pick s.cfg.seed 26 i 500 + (if f.follows.contains i then 1 else 0),
          postsCount := posts fun k => !isMine s.cfg k && authorOf s.cfg k == i }
    s.ok d.toJson

/-- `muteActor` (`mute`) or `unmuteActor`: the AppView applies it with no delay of its own. A
mute of a muted account (an unmute of one that isn't) changes nothing. -/
def Server.setMute (s : Server) (mute : Bool) (actor : String) : Server × Response :=
  match s.resolve actor with
  | none => (s, s.fail 400 "InvalidRequest" "Actor not found")
  | some none => (s, s.fail 400 "InvalidRequest" "Cannot mute oneself")
  | some (some i) =>
    let d := (author s.cfg i).did
    if s.now.muted.contains d == mute then (s, s.ok (.obj []))
    else (s.append (if mute then .mute d else .unmute d) false, s.ok (.obj []))

/-- `getPosts`: the views of the posts on the timeline among `uris` (25 at most). -/
def Server.getPosts (s : Server) (params : List (String × String)) : Response :=
  let uris := (params.filter (·.1 == "uris")).map (·.2)
  if uris.length > maxGetPosts then s.fail 400 "InvalidRequest" "Too many uris"
  else
    let f := s.seen
    let k? (u : String) : Option Nat :=
      match u.splitOn "/" with
      | [_, _, _, _, r] =>
        if r.startsWith "3fk" then (digits 8 (r.drop 3).toString).bind fun k =>
          if k < s.length && postUri s.cfg k == u then some k else none
        else none
      | _ => none
    s.ok ({ posts := uris.filterMap fun u => (k? u).map fun k => viewPost s.cfg f (postView s.cfg k) } : Posts).toJson

/-! ### Notifications -/

def Server.listNotifications (s : Server) (params : List (String × String)) : Response :=
  match limitOf params with
  | none => s.fail 400 "InvalidRequest" "limit must be an integer from 1 to 100"
  | some n =>
    let ns := s.notices
    let answer (before : Option Nat) : Response :=
      let (items, lo) := runPage ns n before
      s.ok ({ notifications := items, cursor := lo.map toString,
              seenAt := s.seenAt.map iso } : NotificationPage).toJson
    match params.lookup "cursor" with
    | none => answer none
    | some cur =>
      match digits 9 cur with
      | some i => if 0 < i && i < ns.length then answer (some i)
                  else s.fail 400 "InvalidRequest" "Malformed cursor"
      | none => s.fail 400 "InvalidRequest" "Malformed cursor"

def Server.unreadCount (s : Server) : Nat := (s.notices.filter (!·.isRead)).length

def Server.updateSeen (s : Server) (body : String) : Server × Response :=
  match (decode body).bind seenAtOf with
  | some t =>
    match parseDatetime t with
    | some ms => if ms < 0 then (s, s.fail 400 "InvalidRequest" "seenAt must be a datetime")
                 else ({ s with seenAt := some ms.toNat }, s.ok (.obj []))
    | none => (s, s.fail 400 "InvalidRequest" "seenAt must be a datetime")
  | none => (s, s.fail 400 "InvalidRequest" "Input must have the property seenAt")

/-- The methods that need the access token, once it is checked (and its HTTP method). -/
def Server.authed (s : Server) (nsid : String) (body : String) (params : List (String × String)) :
    Server × Response :=
  let bad := (s, s.fail 400 "InvalidRequest" "Input is not valid")
  if nsid == nsidGetSession then (s, s.ok (.obj s.accountJson))
  else if nsid == nsidGetTimeline then (s, s.getTimeline params)
  else if nsid == nsidPutRecord then
    match (decode body).bind PutRecord.ofJson with
    | some w => s.putRec w
    | none => bad
  else if nsid == nsidDeleteRecord then
    match (decode body).bind deleteRecordOf with
    | some u => s.deleteRec u
    | none => bad
  else if nsid == nsidGetRecord then
    match params.lookup "repo", params.lookup "collection", params.lookup "rkey" with
    | some repo, some collection, some rkey => (s, s.getRec { repo, collection, rkey })
    | _, _, _ => bad
  else if nsid == nsidMuteActor || nsid == nsidUnmuteActor then
    match (decode body).bind (·.str? "actor") with
    | some a => s.setMute (nsid == nsidMuteActor) a
    | none => bad
  else if nsid == nsidGetProfile then (s, s.getProfile params)
  else if nsid == nsidGetPosts then (s, s.getPosts params)
  else if nsid == nsidListNotifications then (s, s.listNotifications params)
  else if nsid == nsidGetUnreadCount then (s, s.ok (unreadCountJson s.unreadCount))
  else if nsid == nsidUpdateSeen then s.updateSeen body
  else (s, s.fail 501 "MethodNotImplemented" "Method Not Implemented")

/-- The methods that need the access token: queries (GET) and procedures (POST). -/
def queryNsids : List String :=
  [nsidGetSession, nsidGetTimeline, nsidGetRecord, nsidGetProfile, nsidGetPosts,
   nsidListNotifications, nsidGetUnreadCount]
def procedureNsids : List String :=
  [nsidPutRecord, nsidDeleteRecord, nsidMuteActor, nsidUnmuteActor, nsidUpdateSeen]

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
  else if queryNsids.contains nsid || procedureNsids.contains nsid then
    if (if procedureNsids.contains nsid then !post else !get) then
      (s, s.fail 400 "InvalidRequest" "Incorrect HTTP method")
    else match s.check "access" r.authorization with
      | .ok s => s.authed nsid r.body params
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
  | .refused => s.fail 400 "InvalidRequest" "Refused by the fake PDS"
  | .lostAfter => .hang

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
  /-- Another account acts (`Server.act`): on post `post`, or the tester's newest post. -/
  | act (kind : ActKind) (actor : Nat) (post : Option Nat)
  /-- The AppView sees a change 0 to `n` requests after it, from now on. -/
  | lag (n : Nat)
  /-- The AppView catches up: it sees everything now. -/
  | catchup
deriving Repr, DecidableEq, Inhabited

/-- `n` posts arrive at the head, with their notifications. -/
def Server.grow (s : Server) (n : Nat) : Server :=
  ({ s with length := s.length + n } : Server).noticePosts s.length

def Server.control (s : Server) : Control → Server
  | .post n => s.grow n
  | .expire => { s with live := s.live.map fun l => { l with expired := true } }
  | .revoke => { s with live := none }
  | .fail n f => { s with faults := s.faults ++ List.replicate n f }
  | .slow ms => { s with delayMs := ms }
  | .act kind actor post =>
    match post.or s.newestMine with
    | some k => s.act kind actor k
    | none => if kind == .follow then s.act kind actor 0 else s
  | .lag n => { s with lag := n }
  | .catchup => { s with log := s.log.map fun e => { e with vis := min e.vis s.count },
                         lastVis := min s.lastVis s.count }

/-- What `/control/state` answers, and every control endpoint after its change. -/
def Server.stateJson (s : Server) : Json :=
  .obj ([("length", Json.ofNat s.length), ("count", Json.ofNat s.count),
         ("issued", Json.ofNat s.issued)]
    ++ opt "live" (fun (l : Live) => .obj [("gen", Json.ofNat l.gen), ("life", Json.ofNat l.life),
         ("uses", Json.ofNat l.uses), ("expired", .bool l.expired)]) s.live
    ++ [("faults", .arr (s.faults.map fun f => .str f.toString)),
        ("delayMs", Json.ofNat s.delayMs), ("lag", Json.ofNat s.lag),
        ("log", Json.ofNat s.log.length), ("seen", Json.ofNat s.seenLog.length),
        ("records", .arr (s.now.repo.map fun r => .str (recUri s.cfg r))),
        ("muted", .arr (s.now.muted.map Json.str)),
        ("likes", Json.ofNat s.now.likes.length), ("reposts", Json.ofNat s.now.reposts.length),
        ("follows", Json.ofNat s.now.follows.length)]
    ++ opt "seenAt" (fun t => .str (iso t)) s.seenAt)

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
  | "act" => do
    let kind ← ActKind.ofString ((params.lookup "kind").getD "like")
    let actor ← num "actor" 0
    guard (actor < authorNames.length)
    let post ← match params.lookup "post" with
      | none => some none
      | some v => (digits 9 v).map some
    some (.act kind actor post)
  | "lag" => (num "n" 0).map .lag
  | "catchup" => some .catchup
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

/-- Between requests: the posts due arrive (with their notifications), and another account may
act. Then the request is counted. -/
def Server.between (s : Server) : Server :=
  let n := s.count
  let s := ({ s with length := s.length + arrivals s.cfg n, count := n + 1 } : Server).noticePosts s.length
  s.othersAct n

/-- One request. An XRPC request is counted after what happens between requests
(`Server.between`); a fault queued by `Control.fail` answers it instead of the method, except
`lostAfter`, after which the method runs and its reply is lost. Images and control requests
aren't counted. -/
def Server.handle (s : Server) (r : Req) : Server × Response :=
  let (path, params) := splitPath r.path
  if path.startsWith "/xrpc/" then
    let s := s.between
    match s.faults with
    | f :: fs =>
      let s := { s with faults := fs }
      match f with
      | .lostAfter => ((s.xrpc r (path.drop 6).toString params).1, .hang)
      | f => (s, s.faultResponse f)
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

/-! ## As a `cairn fuzz` server

The pieces of `Cairn.Fuzz.Server World` (cairn#260, cairn 0.5.0): the server holds the whole
`World` (the fake PDS and the host's Keychain), so a sequence's requests see one another's
effects, writes included. README, "The fake PDS as a `cairn fuzz` server", has the definition
of `Fake.server` that assembles them once a published cairn has `Cairn.Fuzz.Server`. -/

/-- The post at `uri` on the timeline, if it is one. -/
def Server.postAt? (s : Server) (uri : String) : Option Nat :=
  match uri.splitOn "/" with
  | [_, _, _, _, r] =>
    if r.startsWith "3fk" then (digits 8 (r.drop 3).toString).bind fun k =>
      if k < s.length && postUri s.cfg k == uri then some k else none
    else none
  | _ => none

/-- Whether the tester's repo holds a like of the post at `uri` (the PDS's truth, which the
AppView shows once it catches up). -/
def World.likedBy (w : World) (uri : String) : Bool := !(w.server.now.myLikes uri).isEmpty

/-- Whether the tester's repo holds a repost of the post at `uri`. -/
def World.repostedBy (w : World) (uri : String) : Bool := !(w.server.now.myReposts uri).isEmpty

/-- The post's like count once the AppView catches up: its seeded likes and every like record. -/
def World.likeCount (w : World) (uri : String) : Nat :=
  ((w.server.postAt? uri).map (seededLikes w.server.cfg)).getD 0
    + w.server.now.likeCount uri

/-- Whether the tester has muted the account `did`. -/
def World.muted (w : World) (did : String) : Bool := w.server.now.muted.contains did

/-- When the tester last marked notifications seen (ms since the epoch). -/
def World.seenAt (w : World) : Option Nat := w.server.seenAt

/-- A world for a sequence: a random configuration around `cfg` (its seed, base, arrival, life,
act and lag drawn; its service kept). -/
def worldGen (cfg : Config) : Gen World := do
  let seed ← Gen.below 1000000
  let base ← Gen.range 0 60
  let life ← Gen.range 1 8
  let arrival ← Gen.elem [0, 2, 3, 5]
  let act ← Gen.elem [0, 2, 4, 8]
  let lag ← Gen.elem [0, 1, 2, 5]
  return World.init { cfg with seed, base, life, arrival, act, lag }

/-- The requests the fake answers: XRPC over HTTP. Images stay with `replies`. -/
def handles : Cairn.Request → Bool
  | .http _ url .. => (pathOf url).startsWith "/xrpc/"
  | _ => false

/-- The server (and host) handle request `id`. -/
def serve (w : World) (_id : Nat) (r : Cairn.Request) : Gen (World × Cairn.Reply) :=
  pure (w.send r)

/-- The world acting on its own: posts arriving, another account acting, the AppView catching
up, the token expiring. -/
def tick (w : World) : Gen World := do
  let ctl ← Gen.oneOf [
    (Control.post ·) <$> Gen.range 1 5,
    do return .act (← Gen.elem [.like, .like, .repost, .follow]) (← Gen.below authorNames.length) none,
    pure .catchup, pure .expire]
  return { w with server := w.server.control ctl }

/-- The world in words, for a failure's message. -/
def World.describe (w : World) : String :=
  let s := w.server
  s!"fake PDS seed {s.cfg.seed}: {s.length} posts, request {s.count}, lag {s.lag}, " ++
  s!"{s.log.length} changes ({s.seenLog.length} seen), records {s.now.repo.map (recUri s.cfg)}, " ++
  s!"muted {s.now.muted}, seenAt {s.seenAt.map iso}"

/-- The world with a signed-in session saved in the host's Keychain, as an app finds it at
launch: the session's own `createSession` with the identifier and password of the world's seed
(which an app can't know), sent through the host, which captures both tokens. For a `cairn fuzz`
server whose app resumes at launch: `{ server cfg … with init := World.saved <$> worldGen cfg }`. -/
def World.saved (w : World) : World :=
  let c := w.server.cfg
  match (Session.step {} (.signIn c.service c.identifier c.password)).2 with
  | [.send _ _ r] => (w.send r).1
  | _ => w

/-- The fake PDS as a `cairn fuzz` server (cairn#260). -/
def server {S : Type} (cfg : Config := {})
    (checks drained : List (Cairn.ClaimId × (S → World → Bool)) := []) : Cairn.Fuzz.Server S where
  W := World
  init := worldGen cfg
  handles := handles
  handle := serve
  tick := tick
  checks := checks
  drained := drained
  describe := World.describe

end CairnAtproto.Fake
