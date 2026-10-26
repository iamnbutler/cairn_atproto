module

public import CairnAtproto.Lexicon.Feed
public import CairnAtproto.Lexicon.Notification

/-! # A paged list: `Paged α`

A list the server pages by cursor, newest first, that the app shows and extends: the home feed
(`Paged FeedItem`), notifications (`Paged Notification`). It holds the items, the cursor of the
last page and whether that page was the last (`atEnd`), and the load-more and refresh in flight,
each with the app's call id (`Session.Input.call`). It moved here from Sky's `Feed` (cairn#250)
with its proofs, generic over the item and its key (`Keyed`).

* **Load more** (`beginLoadMore id`, then `gotLoadMore id page`) asks from the cursor the list
  holds; its page is appended only if the list still holds that cursor when it comes, so a page
  for a list that has moved on is dropped.
* **Refresh** (`beginRefresh id`, then `gotRefresh id page`) asks for the head. If the page holds
  the list's first item, the items above it are the new ones and go on top (`newOnTop`); if it
  doesn't (more than a page arrived), the list is replaced by the page and its cursor, and a
  load-more in flight is for a list that is gone (`headPage` forgets it; the app withdraws its
  call, `Session.Input.cancel`). `beginRefresh` also forgets the load-more in flight and says
  which call to withdraw.
* Answers go in as `Option (Page α)`: the page, or `none` if the call failed. `FeedPage.page`
  and `NotificationPage.page` make one; `gotLoadMore` and `gotRefresh` ignore an answer to any
  other call.

**What is proved** (`CairnAtproto.Proofs.Paged`), for any item type, against a server list `T`
(newest first, keys distinct) that only grows at its head; `cairn_atproto^26`–`^29`:

* `run_append`, `headPage_run`, `run_grow`, `run_nodup`: a list that is a contiguous run of `T`
  stays one: when the page that follows it is appended, when a head page of `T` arrives, and
  when new items arrive at the head of `T`; and a run has no duplicates (`Contiguous`, ^26).
* `gotLoadMore_stale`: a load-more page for a cursor the list no longer holds changes nothing it
  shows (^27).
* `CursorKept`: a list with items that isn't at its end holds a cursor; every operation keeps it
  (^28).
* `race`: a refresh and a load-more both in flight, answered in either order, end the same
  (^29). -/

@[expose] public section

namespace CairnAtproto

/-- What identifies an item in the server's list. -/
class Keyed (α : Type) (κ : outParam Type) where
  key : α → κ

/-- A timeline item: its post, and the repost that put it there (`none` for the post itself;
the reposter's DID; `$<type>` for another reason, such as a pin). A post can be in a timeline
once as itself and once per repost. -/
def reasonKey : Option Reason → Option String
  | none => none
  | some (.repost b _) => some b.did
  | some (.other t) => some ("$" ++ t)

def FeedItem.key (i : FeedItem) : String × Option String := (i.post.uri, reasonKey i.reason)

instance : Keyed FeedItem (String × Option String) := ⟨FeedItem.key⟩

/-- A notification: its record's URI. -/
instance : Keyed Notification String := ⟨Notification.uri⟩

/-- A page of a list: its items, newest first, and the cursor of the next (none at the end). -/
structure Page (α : Type) where
  items : List α
  cursor : Option String := none
deriving Repr, DecidableEq, Inhabited

def FeedPage.page (p : FeedPage) : Page FeedItem := ⟨p.feed, p.cursor⟩

def NotificationPage.page (p : NotificationPage) : Page Notification := ⟨p.notifications, p.cursor⟩

section
variable {α κ : Type} [Keyed α κ] [DecidableEq κ]

/-- The keys of a list. -/
def keys (l : List α) : List κ := l.map Keyed.key

/-- The position of the first item with key `k`. -/
def indexOf (k : κ) : List α → Option Nat
  | [] => none
  | x :: xs => if Keyed.key x = k then some 0 else (indexOf k xs).map (· + 1)

/-- A head page against the list: when the page holds the list's first item, the items above it
(the new ones); otherwise `none`. -/
def newOnTop (items page : List α) : Option (List α) :=
  match items with
  | [] => none
  | f :: _ => (indexOf (Keyed.key f) page).map page.take

end

/-- A paged list, newest first. -/
structure Paged (α : Type) where
  /-- Newest first. -/
  items : List α := []
  /-- The cursor that came with the last page: where the next page starts. -/
  cursor : Option String := none
  /-- The last page came without a cursor: there is nothing older. -/
  atEnd : Bool := false
  /-- The load-more in flight: its call id and the cursor it asked from. -/
  loadMore : Option (Nat × String) := none
  /-- The refresh in flight: its call id. -/
  refresh : Option Nat := none
deriving Repr, DecidableEq, Inhabited

namespace Paged
variable {α κ : Type} [Keyed α κ] [DecidableEq κ]

/-- What the list shows: its items, cursor and end. -/
def content (f : Paged α) : List α × Option String × Bool := (f.items, f.cursor, f.atEnd)

def appendPage (f : Paged α) (p : Page α) : Paged α :=
  { f with items := f.items ++ p.items, cursor := p.cursor, atEnd := p.cursor.isNone }

/-- The list replaced by a page: its items and cursor. A load-more in flight was for the old
list. -/
def replaceBy (f : Paged α) (p : Page α) : Paged α :=
  { f with items := p.items, cursor := p.cursor, atEnd := p.cursor.isNone, loadMore := none }

/-- A head page: the new items on top, or the list replaced. -/
def headPage (f : Paged α) (p : Page α) : Paged α :=
  match newOnTop f.items p.items with
  | some new => { f with items := new ++ f.items }
  | none => f.replaceBy p

/-- The answer to call `id`, if it is the load-more in flight: its page, or `none` if it failed.
The page is appended only if the list still holds the cursor it asked from. -/
def gotLoadMore (f : Paged α) (id : Nat) (page : Option (Page α)) : Paged α :=
  match f.loadMore with
  | some (l, c) =>
    if l = id then
      match page with
      | some p => if f.cursor = some c then { f with loadMore := none }.appendPage p
                  else { f with loadMore := none }
      | none => { f with loadMore := none }
    else f
  | none => f

/-- The answer to call `id`, if it is the refresh in flight. -/
def gotRefresh (f : Paged α) (id : Nat) (page : Option (Page α)) : Paged α :=
  if f.refresh = some id then
    match page with
    | some p => { f with refresh := none }.headPage p
    | none => { f with refresh := none }
  else f

/-- Whether a load-more can start: none in flight, items held, not at the end, a cursor. -/
def canLoadMore (f : Paged α) : Bool :=
  f.loadMore.isNone && !f.items.isEmpty && !f.atEnd && f.cursor.isSome

/-- Start a load-more as call `id`: the list with it in flight and the cursor to ask from
(`Call.getTimeline limit (some c)`), or `none` when it can't start. -/
def beginLoadMore (f : Paged α) (id : Nat) : Option (Paged α × String) :=
  match f.canLoadMore, f.cursor with
  | true, some c => some ({ f with loadMore := some (id, c) }, c)
  | _, _ => none

/-- Start a refresh as call `id` (ask for the head: `Call.getTimeline limit none`): the list with
it in flight and the load-more forgotten, and that load-more's call id, to withdraw. `none` when
a refresh is in flight already. -/
def beginRefresh (f : Paged α) (id : Nat) : Option (Paged α × Option Nat) :=
  if f.refresh.isNone then
    some ({ f with loadMore := none, refresh := some id }, f.loadMore.map (·.1))
  else none

/-- The calls in flight: the load-more's and the refresh's ids. -/
def inFlight (f : Paged α) : List Nat := (f.loadMore.map (·.1)).toList ++ f.refresh.toList

end Paged

end CairnAtproto
