module

public import CairnAtproto.Lexicon.Feed
public import CairnAtproto.AtUri

/-! # `com.atproto.repo`: records and writes

The records Sky writes into the signed-in account's repo, and the three calls that write and
read them back, on the account's own PDS:

* **`Record`**: `like` and `repost` (`app.bsky.feed.like`, `app.bsky.feed.repost`: a subject
  post by URI and CID, and `createdAt`), `follow` (`app.bsky.graph.follow`: a subject DID), and
  any other record as `other "$type"`. `Record.collection` is its NSID.
* **`PutRecord`** (`com.atproto.repo.putRecord`): write `record` at `repo/collection/rkey`,
  creating or replacing it. With a key the client chose (a TID it minted), the same write sent
  twice writes once: the call is the same request each time it is built
  (`PutRecord.ofJson_toJson`, `cairn_atproto^20`) and the server treats a second one as a no-op
  (assumed, `cairn_atproto^22`).
* **`deleteRecord`**: by `AtUri`. Deleting a record that isn't there succeeds.
* **`getRecord`**: by `AtUri`; `RecordView` (`uri`, `cid`, `value`), or 400 `RecordNotFound`.
  The authoritative read: the account's own PDS reflects every write it acknowledged
  (assumed, `cairn_atproto^23`), where the AppView's views can lag.

The calls themselves, through the session, are `Session.Call.putRecord`, `deleteRecord` and
`getRecord` (`CairnAtproto.Acts`). -/

@[expose] public section

namespace CairnAtproto
open CairnJson

def nsidLike : String := "app.bsky.feed.like"
def nsidRepost : String := "app.bsky.feed.repost"
def nsidFollow : String := "app.bsky.graph.follow"
def nsidPutRecord : String := "com.atproto.repo.putRecord"
def nsidDeleteRecord : String := "com.atproto.repo.deleteRecord"
def nsidGetRecord : String := "com.atproto.repo.getRecord"

/-- A record in the account's repo, the kinds Sky writes. -/
inductive Record where
  /-- `app.bsky.feed.like` of `subject`. -/
  | like (subject : StrongRef) (createdAt : String)
  /-- `app.bsky.feed.repost` of `subject`. -/
  | repost (subject : StrongRef) (createdAt : String)
  /-- `app.bsky.graph.follow` of the account with DID `subject`. -/
  | follow (subject : String) (createdAt : String)
  /-- Anything else (a post, a block, …), by its `$type`. -/
  | other (type : String)
deriving Repr, DecidableEq, Inhabited

/-- The record's collection: its NSID, as its `$type` says. -/
def Record.collection : Record → String
  | .like .. => nsidLike
  | .repost .. => nsidRepost
  | .follow .. => nsidFollow
  | .other t => t

/-- A like of a post (from a view of it: its URI and CID). -/
def Record.likeOf (p : Post) (createdAt : String) : Record := .like ⟨p.uri, p.cid⟩ createdAt

/-- A repost of a post. -/
def Record.repostOf (p : Post) (createdAt : String) : Record := .repost ⟨p.uri, p.cid⟩ createdAt

/-- A follow of an account. -/
def Record.followOf (did : String) (createdAt : String) : Record := .follow did createdAt

def Record.toJson : Record → Json
  | .like s at_ => .obj [("$type", .str nsidLike), ("subject", s.toJson), ("createdAt", .str at_)]
  | .repost s at_ => .obj [("$type", .str nsidRepost), ("subject", s.toJson), ("createdAt", .str at_)]
  | .follow d at_ => .obj [("$type", .str nsidFollow), ("subject", .str d), ("createdAt", .str at_)]
  | .other t => .obj [("$type", .str t)]

/-- Total: a record of another type, or missing a field, is `other "$type"`. -/
def Record.ofJson (j : Json) : Record :=
  let t := j.type
  let at_ := (j.str? "createdAt").getD ""
  if t = nsidLike then
    (((j.obj? "subject").bind StrongRef.ofJson).map (Record.like · at_)).getD (.other t)
  else if t = nsidRepost then
    (((j.obj? "subject").bind StrongRef.ofJson).map (Record.repost · at_)).getD (.other t)
  else if t = nsidFollow then ((j.str? "subject").map (Record.follow · at_)).getD (.other t)
  else .other t

/-- A `putRecord` write: `record` at `repo/record.collection/rkey`. -/
structure PutRecord where
  /-- The account's DID. -/
  repo : String
  /-- The record key, chosen by the client (a minted TID's text). -/
  rkey : String
  record : Record
deriving Repr, DecidableEq, Inhabited

/-- Where the write puts its record. -/
def PutRecord.uri (w : PutRecord) : AtUri := ⟨w.repo, w.record.collection, w.rkey⟩

/-- `putRecord`'s input, as the request body. -/
def PutRecord.toJson (w : PutRecord) : Json :=
  .obj [("repo", .str w.repo), ("collection", .str w.record.collection), ("rkey", .str w.rkey),
    ("record", w.record.toJson)]

/-- A `putRecord` body read back: the write it asks for (`none` when its collection isn't its
record's). A server, or the fake, reads it this way. -/
def PutRecord.ofJson (j : Json) : Option PutRecord := do
  let repo ← j.str? "repo"
  let collection ← j.str? "collection"
  let rkey ← j.str? "rkey"
  let record ← (j.obj? "record").map Record.ofJson
  if collection = record.collection then some { repo, rkey, record } else none

/-- `deleteRecord`'s input. -/
def deleteRecordJson (u : AtUri) : Json :=
  .obj [("repo", .str u.repo), ("collection", .str u.collection), ("rkey", .str u.rkey)]

/-- A `deleteRecord` body read back. -/
def deleteRecordOf (j : Json) : Option AtUri := do
  let repo ← j.str? "repo"
  let collection ← j.str? "collection"
  let rkey ← j.str? "rkey"
  some { repo, collection, rkey }

/-- `getRecord`'s parameters. -/
def getRecordParams (u : AtUri) : List (String × String) :=
  [("repo", u.repo), ("collection", u.collection), ("rkey", u.rkey)]

/-- `getRecord`'s answer. -/
structure RecordView where
  uri : String
  cid : Option String := none
  value : Record
deriving Repr, DecidableEq, Inhabited

def RecordView.ofJson (j : Json) : Option RecordView := do
  let uri ← j.str? "uri"
  let value ← (j.obj? "value").map Record.ofJson
  some { uri, cid := j.str? "cid", value }

def RecordView.toJson (r : RecordView) : Json :=
  .obj ([("uri", .str r.uri)] ++ opt "cid" Json.str r.cid ++ [("value", r.value.toJson)])

/-- `putRecord`'s answer: the record's URI and CID. -/
def StrongRef.ofPutReply (j : Json) : Option StrongRef := StrongRef.ofJson j

end CairnAtproto
