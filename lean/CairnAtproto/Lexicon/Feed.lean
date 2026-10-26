module

public import CairnAtproto.Xrpc

/-! # `app.bsky.feed`: the timeline

`app.bsky.feed.getTimeline` (and `getAuthorFeed`, which answers the same shape) as Sky reads it:
each `FeedItem` is a post with its author, text, `createdAt`, counts and embed, the post it
replies to, and the repost that put it in the feed; and `getPosts`, the same post views by URI.

**Viewer state.** An authenticated view says how the signed-in account stands to each post
(`Post.viewer`: its own like and repost records) and account (`Profile.viewer`: muted, blocked,
its follow record). A public view has none, and it decodes as the default (nothing); the encoders
write the default as no member, so a fake's views without viewer state are byte-for-byte what
they were.

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

/-- `com.atproto.repo.strongRef`: a record by its AT URI and the CID of the version meant. A like
or repost names its subject this way; a reply its parent and root. -/
structure StrongRef where
  uri : String
  cid : String
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.actor.defs#viewerState`: how the signed-in account (the viewer) stands to an
account. The AppView fills it in only for an authenticated request; a public one has none, which
decodes as the default (nothing). -/
structure ProfileViewer where
  /-- The viewer has muted the account (`app.bsky.graph.muteActor`). -/
  muted : Bool := false
  /-- The account blocks the viewer. -/
  blockedBy : Bool := false
  /-- The viewer's block record of the account (an AT URI), if they block it. -/
  blocking : Option String := none
  /-- The viewer's follow record of the account (an AT URI), if they follow it: what an unfollow
  deletes. -/
  following : Option String := none
  /-- The account's follow record of the viewer, if it follows them. -/
  followedBy : Option String := none
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.actor.defs#profileViewBasic`, the parts Sky shows, and the viewer's state. -/
structure Profile where
  did : String
  handle : String
  displayName : Option String := none
  avatar : Option String := none
  viewer : ProfileViewer := {}
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

/-- `app.bsky.feed.defs#viewerState` of a post: the viewer's own like and repost records of it
(AT URIs), if any. A post view's counts include the viewer's like exactly when `like` is set
(`cairn_atproto^24`, assumed). -/
structure PostViewer where
  like : Option String := none
  repost : Option String := none
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.feed.post#replyRef`, in a post's record: the post it replies to and its thread's
root. -/
structure PostReplyRef where
  root : StrongRef
  parent : StrongRef
deriving Repr, DecidableEq, Inhabited

/-- `app.bsky.feed.defs#postView`, the parts Sky shows. -/
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
  /-- The record's `reply`: set when the post is a reply. -/
  reply : Option PostReplyRef := none
  /-- The viewer's like and repost of it (none on a public, unauthenticated view). -/
  viewer : PostViewer := {}
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

def StrongRef.ofJson (j : Json) : Option StrongRef := do
  let uri ← j.str? "uri"
  let cid ← j.str? "cid"
  some { uri, cid }

/-- Total: a missing or malformed member reads as its default. -/
def ProfileViewer.ofJson (j : Json) : ProfileViewer :=
  { muted := (j.bool? "muted").getD false, blockedBy := (j.bool? "blockedBy").getD false,
    blocking := j.str? "blocking", following := j.str? "following",
    followedBy := j.str? "followedBy" }

/-- A view's `viewer` member; none (a public view) is the default. -/
def ProfileViewer.of (j : Json) : ProfileViewer :=
  ((j.obj? "viewer").map ProfileViewer.ofJson).getD {}

def Profile.ofJson (j : Json) : Option Profile := do
  let did ← j.str? "did"
  let handle ← j.str? "handle"
  some { did, handle, displayName := j.str? "displayName", avatar := j.str? "avatar",
         viewer := ProfileViewer.of j }

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

def PostReplyRef.ofJson (j : Json) : Option PostReplyRef := do
  let root ← (j.obj? "root").bind StrongRef.ofJson
  let parent ← (j.obj? "parent").bind StrongRef.ofJson
  some { root, parent }

/-- The `reply` of a post record (none when absent or malformed). -/
def recordReply (j : Json) : Option PostReplyRef :=
  ((j.obj? "record").bind (·.obj? "reply")).bind PostReplyRef.ofJson

def PostViewer.ofJson (j : Json) : PostViewer :=
  { like := j.str? "like", repost := j.str? "repost" }

def Post.ofJson (j : Json) : Option Post := do
  let uri ← j.str? "uri"
  let cid ← j.str? "cid"
  let author ← (j.obj? "author").bind Profile.ofJson
  let indexedAt ← j.str? "indexedAt"
  let (text, createdAt) := recordText j
  some { uri, cid, author, text, createdAt, embed := (j.obj? "embed").map Embed.ofJson,
         replyCount := (j.nat? "replyCount").getD 0, repostCount := (j.nat? "repostCount").getD 0,
         likeCount := (j.nat? "likeCount").getD 0, quoteCount := (j.nat? "quoteCount").getD 0,
         indexedAt, reply := recordReply j,
         viewer := ((j.obj? "viewer").map PostViewer.ofJson).getD {} }

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

def StrongRef.toJson (r : StrongRef) : Json := .obj [("uri", .str r.uri), ("cid", .str r.cid)]

def ProfileViewer.toJson (v : ProfileViewer) : Json :=
  .obj ([("muted", .bool v.muted), ("blockedBy", .bool v.blockedBy)] ++ opt "blocking" Json.str v.blocking
    ++ opt "following" Json.str v.following ++ opt "followedBy" Json.str v.followedBy)

/-- `some v` unless `v` is the default, which is written as no member at all (as a public view
has none). -/
def nonDefault {α : Type} [DecidableEq α] (d v : α) : Option α := if v = d then none else some v

def Profile.toJson (p : Profile) : Json :=
  .obj ([("did", .str p.did), ("handle", .str p.handle)] ++ opt "displayName" Json.str p.displayName
    ++ opt "avatar" Json.str p.avatar ++ opt "viewer" ProfileViewer.toJson (nonDefault {} p.viewer))

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

def PostReplyRef.toJson (r : PostReplyRef) : Json :=
  .obj [("root", r.root.toJson), ("parent", r.parent.toJson)]

def PostViewer.toJson (v : PostViewer) : Json :=
  .obj (opt "like" Json.str v.like ++ opt "repost" Json.str v.repost)

def Post.toJson (p : Post) : Json :=
  .obj ([("uri", .str p.uri), ("cid", .str p.cid), ("author", p.author.toJson),
    ("record", .obj ([("$type", .str tPostRecord), ("text", .str p.text),
      ("createdAt", .str p.createdAt)] ++ opt "reply" PostReplyRef.toJson p.reply))]
    ++ opt "embed" Embed.toJson p.embed
    ++ [("replyCount", Json.ofNat p.replyCount), ("repostCount", Json.ofNat p.repostCount),
        ("likeCount", Json.ofNat p.likeCount), ("quoteCount", Json.ofNat p.quoteCount),
        ("indexedAt", .str p.indexedAt)]
    ++ opt "viewer" PostViewer.toJson (nonDefault {} p.viewer))

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

/-! ## `getPosts` -/

/-- `app.bsky.feed.getPosts`'s answer: views of the posts asked for that the AppView has (a
deleted post is left out), with the viewer's state and counts. -/
structure Posts where
  posts : List Post
deriving Repr, DecidableEq, Inhabited

def Posts.ofJson (j : Json) : Option Posts := do
  let posts ← (j.arr? "posts").bind (optMap Post.ofJson)
  some { posts }

def Posts.toJson (p : Posts) : Json := .obj [("posts", .arr (p.posts.map Post.toJson))]

/-- How many URIs one `getPosts` takes. -/
def maxGetPosts : Nat := 25

/-! ## Requests -/

def nsidGetTimeline : String := "app.bsky.feed.getTimeline"
def nsidGetAuthorFeed : String := "app.bsky.feed.getAuthorFeed"
def nsidGetPosts : String := "app.bsky.feed.getPosts"

/-- `getPosts`'s parameters: `uris=…` once per URI, the first `maxGetPosts` (25) of them. -/
def getPostsParams (uris : List String) : List (String × String) :=
  (uris.take maxGetPosts).map ("uris", ·)

/-- `limit` and `cursor` parameters. -/
def pageParams (limit : Option Nat) (cursor : Option String) : List (String × String) :=
  (limit.map fun n => ("limit", toString n)).toList ++ (cursor.map fun c => ("cursor", c)).toList

end CairnAtproto
