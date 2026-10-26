module

public import CairnAtproto.Session
public import CairnAtproto.Tid
public import CairnAtproto.Lexicon.Repo
public import CairnAtproto.Lexicon.Actor
public import CairnAtproto.Lexicon.Notification

/-! # Acting: the calls, and how a write's reply is read

The session calls for acting on Bluesky (`Session.Call`, made with `Session.Input.call` like
`Call.getTimeline`; the session sends them to the account's PDS with its access token), and
what their replies mean.

| Call | Request | Answer (read with `Outcome.ofReply`) |
|---|---|---|
| `Call.putRecord w` | POST `com.atproto.repo.putRecord`, `w.toJson` | `StrongRef.ofPutReply`; read as a write: `WriteOutcome.ofReply` |
| `Call.deleteRecord u` | POST `com.atproto.repo.deleteRecord` | a write |
| `Call.getRecord u` | GET `com.atproto.repo.getRecord?repo&collection&rkey` | `ReadBack.ofReply` |
| `Call.muteActor did`, `Call.unmuteActor did` | POST `app.bsky.graph.muteActor` / `unmuteActor` | a write |
| `Call.getProfile actor` | GET `app.bsky.actor.getProfile?actor` | `ProfileDetail.ofJson` |
| `Call.getPosts uris` | GET `app.bsky.feed.getPosts?uris=…` (the first 25) | `Posts.ofJson` |
| `Call.listNotifications limit cursor` | GET `app.bsky.notification.listNotifications` | `NotificationPage.ofJson` |
| `Call.getUnreadCount` | GET `app.bsky.notification.getUnreadCount` | `unreadCountOf` |
| `Call.updateSeen seenAt` | POST `app.bsky.notification.updateSeen` | a write |

**A write's outcome** (`WriteOutcome.ofReply`, `WriteOutcome.ofAnswer`):

* `acked`: a 2xx. The server holds the write.
* `refused status error reset`: any other answer below 500, a 4xx (`RateLimitExceeded` 429
  with its `ratelimit-reset`, `InvalidRequest`, …). The server did not apply it. (A write
  answered `ExpiredToken` is sent once more by the session after a refresh, `cairn_atproto^13`;
  it was not applied the first time, `cairn_atproto^25`, assumed.)
* `lost why`: a 5xx, a timeout, a network failure, or anything else the host says. The write
  may or may not have happened: read it back (`Call.getRecord`, or `getProfile` for a mute)
  before deciding, and don't send it blind again.
* `notSent`: the host never sent it (its Keychain item is missing, or it was denied), or the
  session had no session to send it with (`Answer.signedOut`). Not applied.

**A read-back** (`ReadBack.ofReply`, for `getRecord`): `found view` (a 2xx with the record),
`missing` (400 `RecordNotFound`), or `unsure` (anything else: read again later). -/

@[expose] public section

namespace CairnAtproto
open CairnJson

namespace Session

/-- A procedure call with a JSON body. -/
def Call.procedureJson (nsid : String) (body : Json) : Call :=
  { nsid, procedure := true, body := encode body }

/-- `com.atproto.repo.putRecord`: write `w.record` at `w.repo/collection/w.rkey`, creating or
replacing it. Built from the write alone, so the same write is the same request. -/
def Call.putRecord (w : PutRecord) : Call := Call.procedureJson nsidPutRecord w.toJson

/-- `com.atproto.repo.deleteRecord` of the record at `u`. -/
def Call.deleteRecord (u : AtUri) : Call := Call.procedureJson nsidDeleteRecord (deleteRecordJson u)

/-- `com.atproto.repo.getRecord` of the record at `u`, from the account's PDS: the
authoritative read after a lost write. -/
def Call.getRecord (u : AtUri) : Call := { nsid := nsidGetRecord, params := getRecordParams u }

/-- `app.bsky.graph.muteActor`: mute an account (a DID or handle). -/
def Call.muteActor (actor : String) : Call := Call.procedureJson nsidMuteActor (actorJson actor)

/-- `app.bsky.graph.unmuteActor`. -/
def Call.unmuteActor (actor : String) : Call :=
  Call.procedureJson nsidUnmuteActor (actorJson actor)

/-- `app.bsky.actor.getProfile` of an account (a DID or handle), with the viewer's state. -/
def Call.getProfile (actor : String) : Call := { nsid := nsidGetProfile, params := [("actor", actor)] }

/-- `app.bsky.feed.getPosts`: views of up to 25 posts by URI (the rest are dropped; split a
longer list). -/
def Call.getPosts (uris : List String) : Call := { nsid := nsidGetPosts, params := getPostsParams uris }

/-- `app.bsky.notification.listNotifications`: `limit` (1 to 100; the server's default is 50)
after `cursor`. -/
def Call.listNotifications (limit : Option Nat := none) (cursor : Option String := none) : Call :=
  { nsid := nsidListNotifications, params := pageParams limit cursor }

/-- `app.bsky.notification.getUnreadCount`. -/
def Call.getUnreadCount : Call := { nsid := nsidGetUnreadCount }

/-- `app.bsky.notification.updateSeen`: everything indexed up to `seenAt` (a datetime,
`formatDatetime`) is read. -/
def Call.updateSeen (seenAt : String) : Call := Call.procedureJson nsidUpdateSeen (seenAtJson seenAt)

/-- A `putRecord` call read back: the write it makes, if it is one. -/
def Call.putRecordOf (c : Call) : Option PutRecord :=
  if c.nsid = nsidPutRecord ∧ c.procedure = true then (decode c.body).bind PutRecord.ofJson
  else none

end Session

/-! ## A write's outcome -/

/-- Why a write's outcome is unknown. -/
inductive Lost where
  /-- A 5xx: the server failed, perhaps after applying it. -/
  | server (status : Nat)
  | timeout
  | network
  /-- Any other failure the host reports, or a reply that isn't HTTP. -/
  | other (message : String)
deriving Repr, DecidableEq, Inhabited

/-- What a write (`putRecord`, `deleteRecord`, `muteActor`, `unmuteActor`, `updateSeen`) came to. -/
inductive WriteOutcome where
  /-- 2xx: applied. -/
  | acked
  /-- Below 500 and not 2xx: not applied. `reset` is `ratelimit-reset` (seconds since the epoch)
  when the server sent it. -/
  | refused (status : Nat) (e : XrpcError) (reset : Option Nat)
  /-- Unknown: read it back. -/
  | lost (why : Lost)
  /-- Never sent: not applied. -/
  | notSent
deriving Repr, DecidableEq, Inhabited

/-- How a write's reply is read: 2xx `acked`; any other status below 500 `refused`; 5xx, a
timeout, a network failure or any other failure `lost`; a request the host didn't send (a
missing Keychain item, denied) `notSent`. -/
def WriteOutcome.ofReply : Cairn.Reply → WriteOutcome
  | .http status headers body =>
    if isSuccess status then .acked
    else if status < 500 then .refused status (XrpcError.ofBody body) (ratelimitReset headers)
    else .lost (.server status)
  | .failed .timeout _ => .lost .timeout
  | .failed .network _ => .lost .network
  | .failed .notFound _ => .notSent
  | .failed .denied _ => .notSent
  | .failed _ m => .lost (.other m)
  | _ => .lost (.other "not an http reply")

/-- The session's answer to a write call: its reply read by `ofReply`, or `notSent` when the
session answered `signedOut` (it sent nothing, or what it sent was refused for its token). -/
def WriteOutcome.ofAnswer : Session.Answer → WriteOutcome
  | .reply r => WriteOutcome.ofReply r
  | .signedOut => .notSent

/-- The server applied the write. -/
def WriteOutcome.applied : WriteOutcome → Option Bool
  | .acked => some true
  | .refused .. | .notSent => some false
  | .lost _ => none

/-- Words for a refusal or a loss, for a line like "Couldn't like @alice's post: rate limited,
try again in 40 s". `now` is the time in seconds since the epoch, for the rate limit's wait. -/
def WriteOutcome.describe (o : WriteOutcome) (now : Nat) : String :=
  match o with
  | .acked => "done"
  | .refused _ e reset =>
    match e.name, reset with
    | .rateLimitExceeded, some r => s!"rate limited, try again in {r - now} s"
    | .rateLimitExceeded, none => "rate limited, try again later"
    | .expiredToken, _ | .invalidToken, _ | .authRequired, _ => "your session has ended"
    | .other n, _ =>
      match e.message with
      | some m => if m.isEmpty then (if n.isEmpty then "the server refused it" else n) else m
      | none => if n.isEmpty then "the server refused it" else n
  | .lost (.server s) => s!"the server failed ({s})"
  | .lost .timeout => "it timed out"
  | .lost .network => "the network failed"
  | .lost (.other m) => m
  | .notSent => "not signed in"

/-! ## Reading a record back -/

/-- What `getRecord` says of a record. -/
inductive ReadBack where
  /-- It exists, as `view`. -/
  | found (view : RecordView)
  /-- 400 `RecordNotFound` (404 too): it doesn't. -/
  | missing
  /-- Anything else: no answer, a 5xx, a refusal, a malformed body. Read again later. -/
  | unsure
deriving Repr, DecidableEq, Inhabited

def ReadBack.ofReply : Cairn.Reply → ReadBack
  | .http status _ body =>
    if isSuccess status then
      match (decodeBytes body).bind RecordView.ofJson with
      | some v => .found v
      | none => .unsure
    else if status == 404 ||
        (status == 400 && (XrpcError.ofBody body).name == .other "RecordNotFound") then .missing
    else .unsure
  | _ => .unsure

/-- The session's answer to `getRecord`. -/
def ReadBack.ofAnswer : Session.Answer → ReadBack
  | .reply r => ReadBack.ofReply r
  | .signedOut => .unsure

end CairnAtproto
