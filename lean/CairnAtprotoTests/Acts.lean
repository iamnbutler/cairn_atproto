import CairnAtproto

open CairnJson CairnAtproto CairnAtproto.Session

/-! Record keys, AT URIs, the acting calls, a write's outcome and read-back, notifications and
`Paged`. -/

namespace ActsTests

/-! ## TIDs -/

def tid0 : Tid := ⟨0, 0, by decide, by decide⟩
#guard tid0.encode == "2222222222222"
-- A TID from the atproto spec reads and writes back, and starts with a char below `k` (top bit 0).
#guard (Tid.decode "3jzfcijpj2z2a").map Tid.encode == some "3jzfcijpj2z2a"
#guard (Tid.decode "3jzfcijpj2z2a").isSome
-- Not 13 chars, a char outside the alphabet, or past 2^63: none.
#guard Tid.decode "3jzfcijpj2z2" == none
#guard Tid.decode "3jzfcijpj2z21" == none
#guard Tid.decode "zzzzzzzzzzzzz" == none

-- Minting: strictly increasing even when the clock stands still or steps back, and the text
-- sorts as the keys do.
def mints (now : List Nat) : List Tid :=
  (now.foldl (fun (g, ts) n => match g.mint n with
    | some (t, g') => (g', ts ++ [t]) | none => (g, ts)) (TidClock.new 5, [])).2
def run := mints [1_700_000_000_000_000, 1_700_000_000_000_000, 1_699_999_999_000_000,
                  1_700_000_000_000_007, 1_700_000_000_000_001]
#guard run.length == 5
#guard (run.zip run.tail).all fun (a, b) => a.toNat < b.toNat && a.encode < b.encode
#guard run.all (·.clock == 5)
#guard run.map (·.micros) ==
  [1_700_000_000_000_000, 1_700_000_000_000_001, 1_700_000_000_000_002, 1_700_000_000_000_007,
   1_700_000_000_000_008]
-- Past 2^53 microseconds there is no key.
#guard ((TidClock.new 0).mint tidMicrosBound).isNone

/-! ## AT URIs and dates -/

def likeUri : AtUri := ⟨"did:plc:alice", "app.bsky.feed.like", "3jzfcijpj2z2a"⟩
#guard toString likeUri == "at://did:plc:alice/app.bsky.feed.like/3jzfcijpj2z2a"
#guard AtUri.parse (toString likeUri) == some likeUri
#guard AtUri.parse "at://did:plc:alice/app.bsky.feed.like" == none
#guard AtUri.parse "at://did:plc:alice//x" == none
#guard AtUri.parse "https://did:plc:alice/a/b" == none
#guard formatDatetime 0 == "1970-01-01T00:00:00.000Z"
#guard formatDatetime 1790812800123 == "2026-10-01T00:00:00.123Z"
#guard parseDatetime (formatDatetime 1790812800123) == some 1790812800123

/-! ## The calls -/

def pds := "https://pds.example.com"
def post : Post :=
  { uri := "at://did:plc:bob/app.bsky.feed.post/3k", cid := "bafyp",
    author := { did := "did:plc:bob", handle := "bob.test" }, text := "hi",
    createdAt := "2026-10-01T00:00:00.000Z", indexedAt := "2026-10-01T00:00:00.000Z" }
def like : PutRecord :=
  { repo := "did:plc:alice", rkey := tid0.encode, record := .likeOf post "2026-10-02T00:00:00.000Z" }

#guard urlOf ((Call.putRecord like).http pds) == pds ++ "/xrpc/com.atproto.repo.putRecord"
#guard methodOf ((Call.putRecord like).http pds) == "POST"
#guard (Call.putRecord like).body ==
  "{\"repo\":\"did:plc:alice\",\"collection\":\"app.bsky.feed.like\",\"rkey\":\"2222222222222\"," ++
  "\"record\":{\"$type\":\"app.bsky.feed.like\",\"subject\":{\"uri\":\"at://did:plc:bob/app.bsky.feed.post/3k\"," ++
  "\"cid\":\"bafyp\"},\"createdAt\":\"2026-10-02T00:00:00.000Z\"}}"
-- The same write is the same call, and reads back as itself.
#guard Call.putRecord like == Call.putRecord { like with }
#guard (Call.putRecord like).putRecordOf == some like
#guard like.uri == ⟨"did:plc:alice", "app.bsky.feed.like", "2222222222222"⟩
def follow : PutRecord := { repo := "did:plc:alice", rkey := "3k", record := .followOf "did:plc:bob" "t" }
#guard (Call.putRecord follow).body.contains "app.bsky.graph.follow"
#guard urlOf ((Call.getRecord likeUri).http pds) == pds ++
  "/xrpc/com.atproto.repo.getRecord?repo=did%3Aplc%3Aalice&collection=app.bsky.feed.like&rkey=3jzfcijpj2z2a"
#guard methodOf ((Call.getRecord likeUri).http pds) == "GET"
#guard (Call.deleteRecord likeUri).body ==
  "{\"repo\":\"did:plc:alice\",\"collection\":\"app.bsky.feed.like\",\"rkey\":\"3jzfcijpj2z2a\"}"
#guard (Call.muteActor "did:plc:bob").body == "{\"actor\":\"did:plc:bob\"}"
#guard (Call.unmuteActor "did:plc:bob").nsid == "app.bsky.graph.unmuteActor"
#guard urlOf ((Call.getProfile "bob.test").http pds) == pds ++ "/xrpc/app.bsky.actor.getProfile?actor=bob.test"
#guard (Call.getPosts ((List.range 30).map toString)).params.length == 25
#guard urlOf ((Call.listNotifications (some 30) (some "c")).http pds) ==
  pds ++ "/xrpc/app.bsky.notification.listNotifications?limit=30&cursor=c"
#guard urlOf (Call.getUnreadCount.http pds) == pds ++ "/xrpc/app.bsky.notification.getUnreadCount"
#guard (Call.updateSeen "2026-10-02T00:00:00.000Z").body == "{\"seenAt\":\"2026-10-02T00:00:00.000Z\"}"

/-! ## A write's outcome, a read-back -/

def http (s : Nat) (body : String) (h : List (String × String) := []) : Cairn.Reply :=
  .http s h body.toUTF8
#guard WriteOutcome.ofReply (http 200 "{\"uri\":\"u\",\"cid\":\"c\"}") == .acked
#guard WriteOutcome.ofReply (http 429 "{\"error\":\"RateLimitExceeded\"}" [("ratelimit-reset", "100")])
  matches .refused 429 _ (some 100)
#guard (WriteOutcome.ofReply (http 429 "{\"error\":\"RateLimitExceeded\"}" [("ratelimit-reset", "100")])).describe 60
  == "rate limited, try again in 40 s"
#guard WriteOutcome.ofReply (http 400 "{\"error\":\"InvalidSwap\"}") matches .refused 400 _ none
#guard WriteOutcome.ofReply (http 502 "") == .lost (.server 502)
#guard WriteOutcome.ofReply (.failed .timeout "t") == .lost .timeout
#guard WriteOutcome.ofReply (.failed .network "n") == .lost .network
#guard WriteOutcome.ofReply (.failed .notFound "no item") == .notSent
#guard WriteOutcome.ofAnswer .signedOut == .notSent
#guard (WriteOutcome.ofReply (http 503 "")).applied == none
#guard (WriteOutcome.ofReply (http 400 "{}")).applied == some false
#guard (WriteOutcome.ofReply (http 200 "")).applied == some true

def recordBody := "{\"uri\":\"at://did:plc:alice/app.bsky.feed.like/3k\",\"cid\":\"c\"," ++
  "\"value\":{\"$type\":\"app.bsky.feed.like\",\"subject\":{\"uri\":\"p\",\"cid\":\"pc\"},\"createdAt\":\"t\"}}"
#guard ReadBack.ofReply (http 200 recordBody) ==
  .found { uri := "at://did:plc:alice/app.bsky.feed.like/3k", cid := some "c", value := .like ⟨"p", "pc"⟩ "t" }
#guard ReadBack.ofReply (http 400 "{\"error\":\"RecordNotFound\",\"message\":\"Could not locate record\"}") == .missing
#guard ReadBack.ofReply (http 404 "") == .missing
#guard ReadBack.ofReply (http 400 "{\"error\":\"InvalidRequest\"}") == .unsure
#guard ReadBack.ofReply (http 500 "") == .unsure
#guard ReadBack.ofReply (http 200 "not json") == .unsure
#guard ReadBack.ofReply (.failed .timeout "") == .unsure
#guard (StrongRef.ofPutReply <$> decode "{\"uri\":\"u\",\"cid\":\"c\",\"commit\":{}}") == some (some ⟨"u", "c"⟩)

/-! ## Notifications -/

#guard ["like", "repost", "follow", "mention", "reply", "quote", "starterpack-joined"].all
  fun s => (NotificationReason.ofString s).toString == s
#guard NotificationReason.ofString "verified" == .other "verified"
#guard (decode "{\"count\":3}").bind unreadCountOf == some 3

/-! ## Paged -/

def n (i : Nat) : Notification :=
  { uri := s!"at://x/n/{i}", cid := "c", author := { did := "d", handle := "h" }, reason := .like,
    indexedAt := "t" }
def pg (is : List Nat) (c : Option String) : Page Notification := ⟨is.map n, c⟩

def p0 : Paged Notification := {}
-- First page by refresh.
def p1 := match p0.beginRefresh 1 with | some (f, _) => f.gotRefresh 1 (some (pg [9, 8, 7] (some "c7"))) | none => p0
#guard p1.items.map (·.uri) == [9, 8, 7].map (n · |>.uri)
#guard p1.canLoadMore
-- Load more, then a refresh with two new on top.
def p2 := match p1.beginLoadMore 2 with
  | some (f, c) => if c = "c7" then f.gotLoadMore 2 (some (pg [6, 5] none)) else p1 | none => p1
#guard p2.items.length == 5 && p2.atEnd && !p2.canLoadMore
def p3 := match p2.beginRefresh 3 with | some (f, _) => f.gotRefresh 3 (some (pg [11, 10, 9, 8] (some "c8"))) | none => p2
#guard p3.items.map (·.uri) == [11, 10, 9, 8, 7, 6, 5].map (n · |>.uri)
-- A refresh while a load-more is in flight withdraws it; its late answer is ignored.
def q1 := (p1.beginLoadMore 4).map (·.1) |>.getD p1
#guard q1.inFlight == [4]
def q2 := q1.beginRefresh 5
#guard q2.map (·.2) == some (some 4)
def q3 := match q2 with | some (f, _) => f.gotLoadMore 4 (some (pg [6] none)) | none => q1
#guard q3.items.length == 3 && q3.inFlight == [5]
-- Only one refresh at a time.
#guard (q3.beginRefresh 6).isNone

end ActsTests
