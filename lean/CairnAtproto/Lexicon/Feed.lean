module

public import CairnAtproto.Xrpc

/-! # `app.bsky.feed`: the timeline

`app.bsky.feed.getTimeline` (and `getAuthorFeed`, which answers the same shape) as M4 reads it:
each `FeedItem` is a post with its author, text, `createdAt`, counts and embed, the post it
replies to, and the repost that put it in the feed.

Decoders are total and ignore fields they don't know. A union member whose `$type` they don't
know, or that is missing a field they need, decodes as the union's `other` with its `$type`
(`Embed.other "app.bsky.embed.video#view"`), so a new kind of embed never fails a page. A feed
item without the fields every post has (`uri`, `cid`, an author with `did` and `handle`,
`indexedAt`) fails the whole page: the feed never skips a post silently.

Every type has an encoder, `toJson`, in the server's shape, and `ofJson (toJson v) = some v`
(`CairnAtproto.Proofs.RoundTrip`). -/

@[expose] public section

namespace CairnAtproto
open CairnJson

/-- `app.bsky.actor.defs#profileViewBasic`, the parts M4 shows. -/
structure Profile where
  did : String
  handle : String
  displayName : Option String := none
  avatar : Option String := none
deriving Repr, DecidableEq, Inhabited

/-- One image of `app.bsky.embed.images#view`. -/
structure Image where
  thumb : String
  fullsize : String
  alt : String := ""
  /-- Width and height. -/
  aspect : Option (Nat × Nat) := none
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.embed.external#viewExternal`: a link card. -/
structure External where
  uri : String
  title : String := ""
  description : String := ""
  thumb : Option String := none
deriving Repr, DecidableEq, Inhabited

/-- A quoted post (`app.bsky.embed.record#viewRecord`): enough for one line. -/
structure QuotedPost where
  uri : String
  cid : String
  author : Profile
  text : String := ""
  createdAt : String := ""
  indexedAt : String := ""
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.embed.record#view`'s `record`. -/
inductive Quote where
  | post (p : QuotedPost)
  | notFound (uri : String)
  | blocked (uri : String)
  | detached (uri : String)
  /-- A feed generator, list, labeler, starter pack, or anything newer. -/
  | other (type : String)
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.embed.recordWithMedia#view`'s `media`. -/
inductive Media where
  | images (images : List Image)
  | external (e : External)
  /-- Video, or anything newer. -/
  | other (type : String)
deriving Repr, DecidableEq, Inhabited

/-- A post's embed view. -/
inductive Embed where
  | images (images : List Image)
  | external (e : External)
  | record (q : Quote)
  | recordWithMedia (q : Quote) (m : Media)
  /-- Video, or anything newer. -/
  | other (type : String)
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.feed.defs#postView`, the parts M4 shows. -/
structure Post where
  uri : String
  cid : String
  author : Profile
  /-- The record's `text`. -/
  text : String := ""
  /-- The record's `createdAt`, as written (`parseDatetime` reads it). -/
  createdAt : String := ""
  embed : Option Embed := none
  replyCount : Nat := 0
  repostCount : Nat := 0
  likeCount : Nat := 0
  quoteCount : Nat := 0
  indexedAt : String
deriving Repr, DecidableEq, Inhabited

/-- A reply's parent or root. -/
inductive ReplyRef where
  | post (p : Post)
  | notFound (uri : String)
  | blocked (uri : String)
  | other (type : String)
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.feed.defs#replyRef`. -/
structure ReplyCtx where
  root : ReplyRef
  parent : ReplyRef
  grandparentAuthor : Option Profile := none
deriving Repr, DecidableEq, Inhabited

/-- Why the item is in the feed. -/
inductive Reason where
  /-- `#reasonRepost`: `by` reposted it at `indexedAt`. -/
  | repost (by_ : Profile) (indexedAt : String)
  /-- `#reasonPin` (an author feed's pinned post), or anything newer. -/
  | other (type : String)
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.feed.defs#feedViewPost`. -/
structure FeedItem where
  post : Post
  reply : Option ReplyCtx := none
  reason : Option Reason := none
deriving Repr, DecidableEq, Inhabited

/-- A page of `getTimeline` or `getAuthorFeed`. No `cursor` means the end of the feed. -/
structure FeedPage where
  feed : List FeedItem
  cursor : Option String := none
deriving Repr, DecidableEq, Inhabited

/-! ## `$type`s -/

def tImagesView : String := "app.bsky.embed.images#view"
def tExternalView : String := "app.bsky.embed.external#view"
def tRecordView : String := "app.bsky.embed.record#view"
def tRecordWithMediaView : String := "app.bsky.embed.recordWithMedia#view"
def tViewRecord : String := "app.bsky.embed.record#viewRecord"
def tViewNotFound : String := "app.bsky.embed.record#viewNotFound"
def tViewBlocked : String := "app.bsky.embed.record#viewBlocked"
def tViewDetached : String := "app.bsky.embed.record#viewDetached"
def tPostView : String := "app.bsky.feed.defs#postView"
def tNotFoundPost : String := "app.bsky.feed.defs#notFoundPost"
def tBlockedPost : String := "app.bsky.feed.defs#blockedPost"
def tReasonRepost : String := "app.bsky.feed.defs#reasonRepost"
def tReasonPin : String := "app.bsky.feed.defs#reasonPin"
def tPostRecord : String := "app.bsky.feed.post"

/-! ## Decoding -/

def Profile.ofJson (j : Json) : Option Profile := do
  let did ← j.str? "did"
  let handle ← j.str? "handle"
  some { did, handle, displayName := j.str? "displayName", avatar := j.str? "avatar" }

def aspectOf (j : Json) : Option (Nat × Nat) :=
  match j.obj? "aspectRatio" with
  | some a =>
    match a.nat? "width", a.nat? "height" with
    | some w, some h => some (w, h)
    | _, _ => none
  | none => none

def Image.ofJson (j : Json) : Option Image := do
  let thumb ← j.str? "thumb"
  let fullsize ← j.str? "fullsize"
  some { thumb, fullsize, alt := (j.str? "alt").getD "", aspect := aspectOf j }

def External.ofJson (j : Json) : Option External := do
  let uri ← j.str? "uri"
  some { uri, title := (j.str? "title").getD "", description := (j.str? "description").getD "",
         thumb := j.str? "thumb" }

/-- The `text` and `createdAt` of a post record (`""` when absent). -/
def recordText (j : Json) : String × String :=
  match j.obj? "record" with
  | some r => ((r.str? "text").getD "", (r.str? "createdAt").getD "")
  | none => ("", "")

def QuotedPost.ofJson (j : Json) : Option QuotedPost := do
  let uri ← j.str? "uri"
  let cid ← j.str? "cid"
  let author ← (j.obj? "author").bind Profile.ofJson
  let (text, createdAt) := match j.obj? "value" with
    | some r => ((r.str? "text").getD "", (r.str? "createdAt").getD "")
    | none => ("", "")
  some { uri, cid, author, text, createdAt, indexedAt := (j.str? "indexedAt").getD "" }

def Quote.ofJson (j : Json) : Quote :=
  let t := j.type
  if t = tViewRecord then ((QuotedPost.ofJson j).map .post).getD (.other t)
  else if t = tViewNotFound then ((j.str? "uri").map .notFound).getD (.other t)
  else if t = tViewBlocked then ((j.str? "uri").map .blocked).getD (.other t)
  else if t = tViewDetached then ((j.str? "uri").map .detached).getD (.other t)
  else .other t

def imagesOf (j : Json) : Option (List Image) := (j.arr? "images").bind (optMap Image.ofJson)

def externalOf (j : Json) : Option External := (j.obj? "external").bind External.ofJson

def Media.ofJson (j : Json) : Media :=
  let t := j.type
  if t = tImagesView then ((imagesOf j).map .images).getD (.other t)
  else if t = tExternalView then ((externalOf j).map .external).getD (.other t)
  else .other t

def Embed.ofJson (j : Json) : Embed :=
  let t := j.type
  if t = tImagesView then ((imagesOf j).map .images).getD (.other t)
  else if t = tExternalView then ((externalOf j).map .external).getD (.other t)
  else if t = tRecordView then (((j.obj? "record").map Quote.ofJson).map .record).getD (.other t)
  else if t = tRecordWithMediaView then
    match (j.obj? "record").bind (·.obj? "record"), j.obj? "media" with
    | some q, some m => .recordWithMedia (Quote.ofJson q) (Media.ofJson m)
    | _, _ => .other t
  else .other t

def Post.ofJson (j : Json) : Option Post := do
  let uri ← j.str? "uri"
  let cid ← j.str? "cid"
  let author ← (j.obj? "author").bind Profile.ofJson
  let indexedAt ← j.str? "indexedAt"
  let (text, createdAt) := recordText j
  some { uri, cid, author, text, createdAt, embed := (j.obj? "embed").map Embed.ofJson,
         replyCount := (j.nat? "replyCount").getD 0, repostCount := (j.nat? "repostCount").getD 0,
         likeCount := (j.nat? "likeCount").getD 0, quoteCount := (j.nat? "quoteCount").getD 0,
         indexedAt }

def ReplyRef.ofJson (j : Json) : ReplyRef :=
  let t := j.type
  if t = tNotFoundPost then ((j.str? "uri").map .notFound).getD (.other t)
  else if t = tBlockedPost then ((j.str? "uri").map .blocked).getD (.other t)
  else ((Post.ofJson j).map .post).getD (.other t)

def ReplyCtx.ofJson (j : Json) : Option ReplyCtx := do
  let root ← j.obj? "root"
  let parent ← j.obj? "parent"
  some { root := ReplyRef.ofJson root, parent := ReplyRef.ofJson parent,
         grandparentAuthor := (j.obj? "grandparentAuthor").bind Profile.ofJson }

def Reason.ofJson (j : Json) : Reason :=
  let t := j.type
  if t = tReasonRepost then
    match (j.obj? "by").bind Profile.ofJson, j.str? "indexedAt" with
    | some p, some at_ => .repost p at_
    | _, _ => .other t
  else .other t

def FeedItem.ofJson (j : Json) : Option FeedItem := do
  let post ← (j.obj? "post").bind Post.ofJson
  some { post, reply := (j.obj? "reply").bind ReplyCtx.ofJson,
         reason := (j.obj? "reason").map Reason.ofJson }

def FeedPage.ofJson (j : Json) : Option FeedPage := do
  let feed ← (j.arr? "feed").bind (optMap FeedItem.ofJson)
  some { feed, cursor := j.str? "cursor" }

/-! ## Encoding -/

def Profile.toJson (p : Profile) : Json :=
  .obj ([("did", .str p.did), ("handle", .str p.handle)] ++ opt "displayName" Json.str p.displayName
    ++ opt "avatar" Json.str p.avatar)

def aspectJson (a : Nat × Nat) : Json := .obj [("width", Json.ofNat a.1), ("height", Json.ofNat a.2)]

def Image.toJson (i : Image) : Json :=
  .obj ([("thumb", .str i.thumb), ("fullsize", .str i.fullsize), ("alt", .str i.alt)]
    ++ opt "aspectRatio" aspectJson i.aspect)

def External.toJson (e : External) : Json :=
  .obj ([("uri", .str e.uri), ("title", .str e.title), ("description", .str e.description)]
    ++ opt "thumb" Json.str e.thumb)

def QuotedPost.toJson (q : QuotedPost) : Json :=
  .obj [("$type", .str tViewRecord), ("uri", .str q.uri), ("cid", .str q.cid),
    ("author", q.author.toJson),
    ("value", .obj [("$type", .str tPostRecord), ("text", .str q.text),
      ("createdAt", .str q.createdAt)]),
    ("indexedAt", .str q.indexedAt)]

def Quote.toJson : Quote → Json
  | .post p => p.toJson
  | .notFound u => .obj [("$type", .str tViewNotFound), ("uri", .str u), ("notFound", .bool true)]
  | .blocked u => .obj [("$type", .str tViewBlocked), ("uri", .str u), ("blocked", .bool true)]
  | .detached u => .obj [("$type", .str tViewDetached), ("uri", .str u), ("detached", .bool true)]
  | .other t => .obj [("$type", .str t)]

def imagesJson (is : List Image) : Json :=
  .obj [("$type", .str tImagesView), ("images", .arr (is.map Image.toJson))]

def externalJson (e : External) : Json :=
  .obj [("$type", .str tExternalView), ("external", e.toJson)]

def Media.toJson : Media → Json
  | .images is => imagesJson is
  | .external e => externalJson e
  | .other t => .obj [("$type", .str t)]

def Embed.toJson : Embed → Json
  | .images is => imagesJson is
  | .external e => externalJson e
  | .record q => .obj [("$type", .str tRecordView), ("record", q.toJson)]
  | .recordWithMedia q m => .obj [("$type", .str tRecordWithMediaView),
      ("record", .obj [("record", q.toJson)]), ("media", m.toJson)]
  | .other t => .obj [("$type", .str t)]

def Post.toJson (p : Post) : Json :=
  .obj ([("uri", .str p.uri), ("cid", .str p.cid), ("author", p.author.toJson),
    ("record", .obj [("$type", .str tPostRecord), ("text", .str p.text),
      ("createdAt", .str p.createdAt)])]
    ++ opt "embed" Embed.toJson p.embed
    ++ [("replyCount", Json.ofNat p.replyCount), ("repostCount", Json.ofNat p.repostCount),
        ("likeCount", Json.ofNat p.likeCount), ("quoteCount", Json.ofNat p.quoteCount),
        ("indexedAt", .str p.indexedAt)])

def ReplyRef.toJson : ReplyRef → Json
  | .post p =>
    match p.toJson with
    | .obj kvs => .obj (("$type", .str tPostView) :: kvs)
    | j => j
  | .notFound u => .obj [("$type", .str tNotFoundPost), ("uri", .str u), ("notFound", .bool true)]
  | .blocked u => .obj [("$type", .str tBlockedPost), ("uri", .str u), ("blocked", .bool true)]
  | .other t => .obj [("$type", .str t)]

def ReplyCtx.toJson (r : ReplyCtx) : Json :=
  .obj ([("root", r.root.toJson), ("parent", r.parent.toJson)]
    ++ opt "grandparentAuthor" Profile.toJson r.grandparentAuthor)

def Reason.toJson : Reason → Json
  | .repost p at_ => .obj [("$type", .str tReasonRepost), ("by", p.toJson), ("indexedAt", .str at_)]
  | .other t => .obj [("$type", .str t)]

def FeedItem.toJson (i : FeedItem) : Json :=
  .obj ([("post", i.post.toJson)] ++ opt "reply" ReplyCtx.toJson i.reply
    ++ opt "reason" Reason.toJson i.reason)

def FeedPage.toJson (p : FeedPage) : Json :=
  .obj ([("feed", .arr (p.feed.map FeedItem.toJson))] ++ opt "cursor" Json.str p.cursor)

/-! ## Requests -/

def nsidGetTimeline : String := "app.bsky.feed.getTimeline"
def nsidGetAuthorFeed : String := "app.bsky.feed.getAuthorFeed"

/-- `limit` and `cursor` parameters. -/
def pageParams (limit : Option Nat) (cursor : Option String) : List (String × String) :=
  (limit.map fun n => ("limit", toString n)).toList ++ (cursor.map fun c => ("cursor", c)).toList

end CairnAtproto
