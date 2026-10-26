module

public import Cairn.Claims.Core
meta import Cairn.Claims.Elab
public import CairnAtproto.Proofs.Tid
public import CairnAtproto.Proofs.Paged
public import CairnAtproto.Proofs.Acts
public import CairnAtproto.Proofs.Fake

/-! # Acting's claims

The claims about acting on Bluesky (`cairn_atproto^17`–`^33`): record keys, writes and how their
replies are read, the paged list, the decoders, what the client assumes of the server, and what
the fake PDS (`CairnAtproto.Fake`) proves of itself.

Record keys are stated over a harness `machine` whose state is a TID minter and the keys it has
minted, newest first, and whose one move mints a key at any clock reading. The other invariants
are facts of every value (any write, any reply, any item type), stated over the same machine as
Cairn states its framework facts over the fixture's: they hold in every state because they don't
depend on it.

| Id | Kind | Claim |
|---|---|---|
| ^17 | move | mint a record key at a clock reading |
| ^18 | invariant | the keys a session mints strictly increase, whatever the clock reads |
| ^19 | invariant | a key's text is 13 characters of the sortable alphabet and reads back as its time and clock id |
| ^20 | invariant | a `putRecord` call is built from the write alone and reads back as it |
| ^21 | invariant | a write's reply: 2xx acked, below 500 refused, 5xx/timeout/network lost |
| ^22 | assume | `putRecord` with a key, and `deleteRecord`, are idempotent |
| ^23 | assume | `getRecord` on the account's own PDS reflects every acknowledged write |
| ^24 | assume | a post view's counts and `viewer` are from the same moment |
| ^25 | assume | a write refused with `ExpiredToken` was not applied |
| ^26 | invariant | a paged list is a contiguous run of the server's |
| ^27 | invariant | a stale load-more page changes nothing |
| ^28 | invariant | the cursor is never lost |
| ^29 | invariant | a refresh racing a load-more ends the same in either order |
| ^30 | invariant | the decoders read back what the encoders write |
| ^31 | invariant | the fake's writes are idempotent and getRecord reads them back |
| ^32 | invariant | the fake's like and repost counts are the records', with the viewer's from the same moment |
| ^33 | invariant | the fake's notification pages are contiguous runs, newest first |

The assumptions' checks run against the fake PDS once it holds a repo (cairn#251, which proves
them of its Lean model) and once against the real network with the installed app (cairn#258). -/

@[expose] public section

namespace CairnAtproto.ActClaims
open Cairn Cairn.Claims CairnAtproto

/-- The harness's state: a minter and the keys it minted, newest first. -/
structure Minting where
  clock : TidClock := TidClock.new 0
  keys : List Tid := []
deriving Inhabited

/-- Mint a key at clock reading `now`; past `2^53` µs nothing is minted. -/
def Minting.mint (s : Minting) (now : Nat) : Minting :=
  match s.clock.mint now with
  | some (t, g) => { clock := g, keys := t :: s.keys }
  | none => s

theorem Minting.mint_keeps (s : Minting) (now : Nat) (h : Minted s.clock s.keys) :
    Minted (s.mint now).clock (s.mint now).keys := by
  have := Minted.mint h now
  unfold Minting.mint
  split <;> simp_all

move ^17 mintMove (s : Minting) (now : Nat) "Mint a record key" where
  does "Mint a record key (a TID) at clock reading now, in microseconds since the epoch."
  sees "A new key is minted, past every key minted before it, or (after the year 2255) none."
  on press
    apply := s.mint now
    post s' := s'.keys = s.keys ∨
      ∃ t, s'.keys = t :: s.keys ∧ ∀ l, s.clock.last = some l → l < t.micros
    sound := by
      intro s now
      simp only [mintMove.press.apply, mintMove.press.post, Minting.mint]
      split
      · next t g h => exact Or.inr ⟨t, rfl, fun l hl => TidClock.mint_increasing h l hl⟩
      · exact Or.inl rfl

def machine : Machine Minting := { init := {}, moves := moves% }

theorem update_keeps : ∀ s a, Minted s.clock s.keys →
    Minted (machine.update s a).1.clock (machine.update s a).1.keys :=
  machine.preserves (P := fun s => Minted s.clock s.keys) <|
    Move.all_cons (mintMove.preserves _ fun s now h => Minting.mint_keeps s now h) Move.all_nil

invariant ^18 keysIncrease "Record keys strictly increase" for machine where
  does "The record keys (TIDs) a session mints strictly increase, as numbers and so as text, and so are distinct, whatever the clock reads: when it stands still or steps back, the next key is one microsecond past the last. All carry the session's clock id."
  holds s := Minted s.clock s.keys
  init := Minted.new 0
  step := update_keeps
  receive := fun _ _ h => h

/-- What ^19 claims of every TID. -/
def TidText : Prop :=
  ∀ t : Tid, t.encode.length = 13 ∧ (∀ c ∈ t.encode.toList, c ∈ tidAlphabet) ∧
    Tid.decode t.encode = some t

theorem tidText : TidText := fun t => ⟨t.encode_length, t.encode_chars, t.decode_encode⟩

invariant ^19 tidReadsBack "A record key's text reads back" for machine where
  does "Every record key (TID) is written as 13 characters of the sortable base-32 alphabet (234567abcdefghijklmnopqrstuvwxyz), and reads back as its time in microseconds and its clock id."
  holds _s := TidText
  init := tidText
  step := fun _ _ _ => tidText
  receive := fun _ _ _ => tidText

/-- What ^20 claims of every write. -/
def SameWrite : Prop :=
  ∀ w : PutRecord, (Session.Call.putRecord w).nsid = nsidPutRecord ∧
    (Session.Call.putRecord w).procedure = true ∧
    (Session.Call.putRecord w).body = CairnJson.encode w.toJson ∧ PutRecord.ofJson w.toJson = some w

theorem sameWrite : SameWrite := Session.Call.putRecord_body

invariant ^20 sameWriteInv "The same write is the same request" for machine where
  does "A record's putRecord call is built from the write alone (repo, record key, record): a POST to com.atproto.repo.putRecord whose body is the write's JSON, which reads back as the write. So the call built again for the same key and record is the same request, and sending it twice is the same write."
  holds _s := SameWrite
  init := sameWrite
  step := fun _ _ _ => sameWrite
  receive := fun _ _ _ => sameWrite

invariant ^21 writeReading "How a write's reply is read" for machine where
  does "A write's reply (putRecord, deleteRecord, muteActor, unmuteActor, updateSeen) is read as acknowledged exactly on a 2xx; refused, with its error and the rate limit's reset, on any other status below 500; lost (applied or not: read it back) on a 5xx, a timeout or a network failure; not sent when the host never sent it or the session was signed out."
  holds _s := WriteReading
  init := writeReading
  step := fun _ _ _ => writeReading
  receive := fun _ _ _ => writeReading

assume ^22 idempotentWrites "Writes with a chosen key are idempotent" where
  does "A com.atproto.repo.putRecord with a record key already written with the same record changes nothing, and a deleteRecord of a record that isn't there succeeds and changes nothing. So a write sent twice (a retry after a lost reply) is written once. Checked against the fake PDS, whose Lean model proves it of itself (cairn#251), and once against the real network (cairn#258)."
  check "atproto.idempotent-writes"

assume ^23 readYourWrites "getRecord reads your writes" where
  does "com.atproto.repo.getRecord on the account's own PDS reflects every write that PDS acknowledged (read-your-writes), where the AppView's views (timeline, getPosts, getProfile, notifications) may lag. So a write whose reply was lost is settled by reading its record back. Checked against the fake PDS (cairn#251) and once against the real network (cairn#258)."
  check "atproto.read-your-writes"

assume ^24 countWithViewer "A post's counts and viewer are from one moment" where
  does "A post view's like and repost counts and its viewer state are from the same moment: the like count includes the viewer's own like exactly when viewer.like is set, and the repost count their repost exactly when viewer.repost is. So a client shows count - [viewer.like] + [shown liked]. Checked against the fake PDS (cairn#251) and once against the real network (cairn#258)."
  check "atproto.count-viewer"

assume ^25 expiredNotApplied "A write refused for its token was not applied" where
  does "A write the server answers 400 ExpiredToken was not applied, so the session's one resend after a refresh (cairn_atproto^12, ^13) writes it at most once. Checked against the fake PDS (cairn#251) and once against the real network (cairn#258)."
  check "atproto.expired-not-applied"

/-! ## The paged list, for any item type -/

/-- ^26, over every item type and key. -/
def PagedContiguous : Prop :=
  ∀ (α κ : Type) [Keyed α κ] [DecidableEq κ], Paged.Contiguous α

theorem pagedContiguous : PagedContiguous := fun _ _ _ _ => Paged.contiguous

invariant ^26 pagedRun "A paged list is a run of the server's" for machine where
  does "A paged list (the feed, notifications: any item type with keys distinct in the server's list) is a contiguous run of the server's list, in its order: no item twice, none skipped. A list that is a run stays one when the next page is appended, when a head page puts new items on top or replaces it, and when new items arrive at the server's head."
  holds _s := PagedContiguous
  init := pagedContiguous
  step := fun _ _ _ => pagedContiguous
  receive := fun _ _ _ => pagedContiguous

/-- ^27, over every item type. -/
def PagedStale : Prop :=
  ∀ (α κ : Type) [Keyed α κ] [DecidableEq κ] (f : Paged α) (id : Nat) (page : Option (Page α)),
    (∀ c, f.loadMore = some (id, c) → f.cursor ≠ some c) →
    (f.gotLoadMore id page).content = f.content

theorem pagedStale : PagedStale := fun _ _ _ _ f id page h => Paged.gotLoadMore_stale f id page h

invariant ^27 pagedStaleInv "A stale page changes nothing" for machine where
  does "In a paged list of any item type, a load-more page asked from a cursor the list no longer holds (a refresh replaced it meanwhile) never changes its items, cursor or end; nor does an answer to any call but the load-more in flight."
  holds _s := PagedStale
  init := pagedStale
  step := fun _ _ _ => pagedStale
  receive := fun _ _ _ => pagedStale

/-- ^28, over every item type: every operation keeps the cursor of a list that isn't at its end. -/
def PagedCursorKept : Prop :=
  ∀ (α κ : Type) [Keyed α κ] [DecidableEq κ] (f : Paged α), Paged.CursorKept f →
    (∀ p, Paged.CursorKept (f.appendPage p)) ∧ (∀ p, Paged.CursorKept (f.headPage p)) ∧
    (∀ id p, Paged.CursorKept (f.gotLoadMore id p)) ∧ (∀ id p, Paged.CursorKept (f.gotRefresh id p)) ∧
    (∀ id g c, f.beginLoadMore id = some (g, c) → Paged.CursorKept g) ∧
    (∀ id g w, f.beginRefresh id = some (g, w) → Paged.CursorKept g)

theorem pagedCursorKept : PagedCursorKept := fun _ _ _ _ f h =>
  ⟨Paged.cursorKept_append f, Paged.cursorKept_headPage h, Paged.cursorKept_gotLoadMore h,
   Paged.cursorKept_gotRefresh h, Paged.cursorKept_beginLoadMore h, Paged.cursorKept_beginRefresh h⟩

invariant ^28 pagedCursor "The cursor is never lost" for machine where
  does "A paged list with items that isn't at its end holds a cursor (where its next page starts), and the empty list does trivially: appending a page, a head page, a load-more's or refresh's answer and starting either keep it."
  holds _s := PagedCursorKept ∧ ∀ (α κ : Type) [Keyed α κ] [DecidableEq κ],
    Paged.CursorKept ({} : Paged α)
  init := ⟨pagedCursorKept, fun _ _ _ _ => Paged.cursorKept_empty⟩
  step := fun _ _ _ => ⟨pagedCursorKept, fun _ _ _ _ => Paged.cursorKept_empty⟩
  receive := fun _ _ _ => ⟨pagedCursorKept, fun _ _ _ _ => Paged.cursorKept_empty⟩

/-- ^29, over every item type. -/
def PagedRace : Prop :=
  ∀ (α κ : Type) [Keyed α κ] [DecidableEq κ] (f : Paged α) (l r : Nat) (c : String)
    (pl pr : Option (Page α)),
    f.loadMore = some (l, c) → f.cursor = some c → f.items ≠ [] → f.refresh = some r →
    (f.gotLoadMore l pl).gotRefresh r pr = (f.gotRefresh r pr).gotLoadMore l pl

theorem pagedRace : PagedRace :=
  fun _ _ _ _ f l r c pl pr hl hc hne hr => Paged.race f l r c pl pr hl hc hne hr

invariant ^29 pagedRaceInv "A refresh racing a load-more" for machine where
  does "In a paged list of any item type, with a load-more and a refresh both in flight, their answers in either order (or either failing) leave the same list."
  holds _s := PagedRace
  init := pagedRace
  step := fun _ _ _ => pagedRace
  receive := fun _ _ _ => pagedRace

/-! ## Decoders -/

/-- ^30: every new encoder's output decodes to its value (decoders are total by construction:
structural Lean functions, replayed by the kernel). -/
def ReadsBack : Prop :=
  (∀ v : Profile, Profile.ofJson v.toJson = some v) ∧
  (∀ v : Post, Post.ofJson v.toJson = some v) ∧
  (∀ v : Posts, Posts.ofJson v.toJson = some v) ∧
  (∀ v : ProfileDetail, ProfileDetail.ofJson v.toJson = some v) ∧
  (∀ v : Record, Record.ofJson v.toJson = v) ∧
  (∀ v : PutRecord, PutRecord.ofJson v.toJson = some v) ∧
  (∀ v : AtUri, deleteRecordOf (deleteRecordJson v) = some v) ∧
  (∀ v : RecordView, RecordView.ofJson v.toJson = some v) ∧
  (∀ v : NotificationPage, (∀ n ∈ v.notifications, n.reason.Canonical) →
    NotificationPage.ofJson v.toJson = some v) ∧
  (∀ n, unreadCountOf (unreadCountJson n) = some n) ∧
  (∀ s, seenAtOf (seenAtJson s) = some s) ∧
  (∀ u : AtUri, u.Valid → AtUri.parse u.toString = some u)

theorem readsBack : ReadsBack :=
  ⟨Profile.ofJson_toJson, Post.ofJson_toJson, Posts.ofJson_toJson, ProfileDetail.ofJson_toJson,
   Record.ofJson_toJson, PutRecord.ofJson_toJson, deleteRecordOf_json, RecordView.ofJson_toJson,
   NotificationPage.ofJson_toJson, unreadCountOf_json, seenAtOf_json, AtUri.parse_toString⟩

invariant ^30 readsBackInv "The decoders read back what the encoders write" for machine where
  does "Every lexicon type added for acting decodes what its encoder writes: profiles and posts with the viewer's state, getPosts' and getProfile's answers, records, putRecord and deleteRecord bodies, getRecord's answer, notification pages (reasons as written), the unread count, updateSeen's body, and AT URIs. Through text too (CairnAtprotoProofs.Text). The decoders are total, and every fixture decodes (make fixtures)."
  holds _s := ReadsBack
  init := readsBack
  step := fun _ _ _ => readsBack
  receive := fun _ _ _ => readsBack

/-! ## The fake PDS (cairn#251)

What the fake's Lean model proves of itself (`CairnAtproto.Proofs.Fake`), so the assumptions
^22–^24 hold of it by proof; `make fake-fuzz` checks them, and ^25, through the session and the
host, and `make fake-pds-replay` checks that the Bun server answers as the model does. -/

invariant ^31 fakeWrites "The fake's writes are idempotent and read back" for machine where
  does "In the fake PDS's model, a putRecord sent twice leaves the server as once, and so does a deleteRecord; deleting a record that isn't there changes nothing; after a 200 putRecord the repo holds the record at its key, after a 200 deleteRecord it holds none; and getRecord answers the record the repo holds now, RecordNotFound when there is none, whatever the AppView's lag. So ^22 and ^23 hold of the fake."
  holds _s := Fake.WritesHold
  init := Fake.writesHold
  step := fun _ _ _ => Fake.writesHold
  receive := fun _ _ _ => Fake.writesHold

invariant ^32 fakeCounts "The fake's counts are its like records" for machine where
  does "In the fake PDS's model, a post view's like count is its seeded likes plus every like record the AppView shows (other accounts' and the tester's), and viewer.like is set exactly when the tester's like is among them; the same for reposts. Counts and viewer state come from one run of the log, so ^24 holds of the fake."
  holds _s := Fake.CountsHold
  init := Fake.countsHold
  step := fun _ _ _ => Fake.countsHold
  receive := fun _ _ _ => Fake.countsHold

invariant ^33 fakeNotices "The fake's notification pages are runs" for machine where
  does "In the fake PDS's model, a listNotifications page is a contiguous run of the notifications the AppView shows, newest first: the head page is the newest, and the page from a cursor is the next ones after it, none skipped or repeated. New notifications only arrive at the head, so a cursor keeps meaning the same place."
  holds _s := Fake.NoticesRun
  init := Fake.noticesRun
  step := fun _ _ _ => Fake.noticesRun
  receive := fun _ _ _ => Fake.noticesRun

def claimInfos : List ClaimInfo := claims%

end CairnAtproto.ActClaims
