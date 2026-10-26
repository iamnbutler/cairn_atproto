module

public import CairnAtproto.Lexicon.Feed

/-! # `app.bsky.notification`

* **`listNotifications`**: a page of `Notification`s, newest first, with a `cursor` for the
  next (none at the end) and the account's `seenAt`. Page it with `Paged Notification`
  (`CairnAtproto.Paged`; a notification's key is its `uri`).
* **`getUnreadCount`**: `{"count": n}`, the notifications indexed after `seenAt`.
* **`updateSeen`**: `{"seenAt": <datetime>}`: everything up to then is read. 200, no body.

A `Notification` is what someone did to the account: its `reason` (`like`, `repost`, `follow`,
`mention`, `reply`, `quote`, or any other as `other "<reason>"`), who did it (`author`, with
the viewer's state), the record it made (`uri`, `cid`; the text, for a reply, mention or quote),
the subject it acted on (`reasonSubject`: the liked or reposted post's URI), whether it is read
and when it was indexed.

The calls are `Session.Call.listNotifications`, `getUnreadCount` and `updateSeen`
(`CairnAtproto.Acts`). -/

@[expose] public section

namespace CairnAtproto
open CairnJson

def nsidListNotifications : String := "app.bsky.notification.listNotifications"
def nsidGetUnreadCount : String := "app.bsky.notification.getUnreadCount"
def nsidUpdateSeen : String := "app.bsky.notification.updateSeen"

/-- Why a notification is there. -/
inductive NotificationReason where
  | like
  | repost
  | follow
  | mention
  | reply
  | quote
  /-- `starterpack-joined`, `like-via-repost`, `verified`, or anything newer, as written. -/
  | other (reason : String)
deriving Repr, DecidableEq, Inhabited

def NotificationReason.ofString : String → NotificationReason
  | "like" => .like
  | "repost" => .repost
  | "follow" => .follow
  | "mention" => .mention
  | "reply" => .reply
  | "quote" => .quote
  | s => .other s

def NotificationReason.toString : NotificationReason → String
  | .like => "like"
  | .repost => "repost"
  | .follow => "follow"
  | .mention => "mention"
  | .reply => "reply"
  | .quote => "quote"
  | .other s => s

/-- A reason reads back as itself when written as `ofString` reads it (`other "like"` is
`like`). -/
def NotificationReason.Canonical (r : NotificationReason) : Prop :=
  NotificationReason.ofString r.toString = r

/-- The record type a reason's notification carries (for writing one, as a fake server does). -/
def NotificationReason.recordType : NotificationReason → String
  | .like => "app.bsky.feed.like"
  | .repost => "app.bsky.feed.repost"
  | .follow => "app.bsky.graph.follow"
  | _ => tPostRecord

/-- `app.bsky.notification.listNotifications#notification`, the parts Sky reads. -/
structure Notification where
  /-- The record the author made (their like, repost, follow, or post). -/
  uri : String
  cid : String
  author : Profile
  reason : NotificationReason
  /-- What it acted on: the liked or reposted post's URI. -/
  reasonSubject : Option String := none
  /-- The record's `text`, for a reply, mention or quote (a post); none for a like or follow. -/
  text : Option String := none
  isRead : Bool := false
  indexedAt : String
deriving Repr, DecidableEq, Inhabited

/-- A page of `listNotifications`. No `cursor` means the end. -/
structure NotificationPage where
  notifications : List Notification
  cursor : Option String := none
  /-- When the account last marked its notifications seen. -/
  seenAt : Option String := none
deriving Repr, DecidableEq, Inhabited

def Notification.ofJson (j : Json) : Option Notification := do
  let uri ← j.str? "uri"
  let cid ← j.str? "cid"
  let author ← (j.obj? "author").bind Profile.ofJson
  let reason ← j.str? "reason"
  let indexedAt ← j.str? "indexedAt"
  some { uri, cid, author, reason := NotificationReason.ofString reason,
         reasonSubject := j.str? "reasonSubject",
         text := (j.obj? "record").bind (·.str? "text"),
         isRead := (j.bool? "isRead").getD false, indexedAt }

/-- The record is written with its type, its text (if any) and `createdAt` = `indexedAt`. -/
def Notification.toJson (n : Notification) : Json :=
  .obj ([("uri", .str n.uri), ("cid", .str n.cid), ("author", n.author.toJson),
    ("reason", .str n.reason.toString)] ++ opt "reasonSubject" Json.str n.reasonSubject ++
    [("record", .obj ([("$type", .str n.reason.recordType)] ++ opt "text" Json.str n.text ++
       [("createdAt", .str n.indexedAt)])),
     ("isRead", .bool n.isRead), ("indexedAt", .str n.indexedAt)])

def NotificationPage.ofJson (j : Json) : Option NotificationPage := do
  let ns ← (j.arr? "notifications").bind (optMap Notification.ofJson)
  some { notifications := ns, cursor := j.str? "cursor", seenAt := j.str? "seenAt" }

def NotificationPage.toJson (p : NotificationPage) : Json :=
  .obj ([("notifications", .arr (p.notifications.map Notification.toJson))] ++
    opt "cursor" Json.str p.cursor ++ opt "seenAt" Json.str p.seenAt)

/-- `getUnreadCount`'s answer. -/
def unreadCountOf (j : Json) : Option Nat := j.nat? "count"

def unreadCountJson (n : Nat) : Json := .obj [("count", Json.ofNat n)]

/-- `updateSeen`'s input. -/
def seenAtJson (seenAt : String) : Json := .obj [("seenAt", .str seenAt)]

/-- An `updateSeen` body read back. -/
def seenAtOf (j : Json) : Option String := j.str? "seenAt"

end CairnAtproto
