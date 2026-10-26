# cairn_atproto

The AT Protocol (Bluesky) for [Cairn](https://github.com/iamnbutler/cairn) apps, in pure Lean:
XRPC requests and errors, lexicon types and decoders (on
[cairn_json](https://github.com/iamnbutler/cairn_json)), RFC 3339 dates, a session machine,
record keys and writes (like, repost, follow, mute) with how their replies are read,
notifications, and a paged list (`Paged`), with proofs. Registry package `cairn_atproto`, Lean library `CairnAtproto`, claim scope
`cairn_atproto`. No Swift, no host code, no `@[extern]`.

**Tokens never reach Lean.** Sign-in and refresh replies have their `accessJwt` and
`refreshJwt` captured by the host into the Keychain items `access` and `refresh` (cairn#205), and
calls name the item that authorises them. No type here has a field for a token, and this
repository holds no credentials, tokens or private timelines: fixtures are recorded *public*
responses or synthesized.

```lean
-- lean/lakefile.lean, after `cairn add cairn_atproto`
require "iamnbutler" / "cairn_atproto" @ "^0.3.0"

import CairnAtproto
open CairnAtproto CairnAtproto.Session

-- A public feed, no session: GET https://public.api.bsky.app/xrpc/app.bsky.feed.getAuthorFeed?actor=bsky.app&limit=30
query "https://public.api.bsky.app" nsidGetAuthorFeed (("actor", "bsky.app") :: pageParams (some 30) none)

-- Its reply, read: .ok page, .error status e reset, .malformed status, .failed fault msg
Outcome.ofReply FeedPage.ofJson reply

-- The session: feed it the app's inputs and the host's replies; send what it says.
let (s, outs) := step init (.signIn "https://bsky.social" "alice.example.com" appPassword)
-- outs = [.send 0 .signIn (createSession …)]   (capture both tokens; the request is `redact`)
let (s, outs) := step s (.reply 0 reply)        -- [.event (.signedIn account)]
let (s, outs) := step s (.call 7 (Call.getTimeline (some 50)))
-- [.send 1 (.call 0) (.http "GET" "<pds>/xrpc/app.bsky.feed.getTimeline?limit=50" … (some (Secret.bearer "access")))]
let (s, outs) := step s (.cancel [7])           -- [.cancel 1]: the app no longer wants call 7

-- The app sends each `Out` as Cairn effects, under ids it keeps apart from its own:
--   .send rid _ r   ↦ Effect.request rid r        .forget rid item ↦ Effect.request rid (.forgetSecret item)
--   .cancel rid     ↦ Effect.cancelRequest rid    and hands every reply back as `.reply rid r`.
```

## What's in it

### XRPC (`CairnAtproto.Xrpc`)

| | |
|---|---|
| Requests | Cairn's own `Request.http` (Cairn 0.3.0): `secret := some (Secret.bearer item)` puts `Authorization: Bearer <item's value>` on it as the host sends it, `capture` lists the reply fields the host writes to Keychain items and blanks, `redact` keeps it out of every dump and log |
| `accessItem`, `refreshItem` | `"access"`, `"refresh"` |
| `query service nsid params secret` | GET `service/xrpc/nsid?params` |
| `procedure service nsid body secret capture redact` | POST with a JSON body |
| `secretOf`, `itemOf`, `captureOf`, `urlOf`, `methodOf`, `bodyOf` | read a request back (`itemOf`: the Keychain item its secret names) |
| `xrpcUrl`, `queryString`, `percentEncode` | URLs: RFC 3986 unreserved characters kept, everything else `%XX` of its UTF-8 bytes |
| `ErrorName` | `expiredToken`, `invalidToken`, `authRequired`, `rateLimitExceeded`, `other name` |
| `XrpcError.ofJson`, `ofBody`, `toJson` | `{"error", "message"}`; a body that isn't one is `other ""` |
| `ratelimitReset headers` | `ratelimit-reset` (any case), in seconds since the epoch |
| `Outcome α`, `Outcome.ofReply decode reply` | `ok v`, `error status e reset`, `malformed status`, `failed fault message`, `notSent` |
| `isSuccess`, `errorOf reply` | 2xx; the error name of a non-2xx reply |

### Lexicons (`CairnAtproto.Lexicon.Server`, `CairnAtproto.Lexicon.Feed`)

| | |
|---|---|
| `SessionInfo` | `did`, `handle`, `email?`, `active?`, `pds?` (the DID document's `#atproto_pds` endpoint). No tokens |
| `createSession service identifier password` | captures both tokens; the one request that carries the password, marked `redact` |
| `refreshSession service`, `getSession service` | authorised by `refresh` (POST, no body, captures both) and by `access` |
| `FeedPage` | `feed : List FeedItem`, `cursor?` (none at the end) |
| `FeedItem` | `post`, `reply? : ReplyCtx` (root, parent, grandparent author), `reason? : Reason` (`repost by indexedAt`, `other type`) |
| `Post` | `uri`, `cid`, `author : Profile`, record `text` and `createdAt`, `embed?`, reply/repost/like/quote counts, `indexedAt`, `reply? : PostReplyRef` (the record's `reply`: root and parent `StrongRef`s), `viewer : PostViewer` |
| `PostViewer` | `like?`, `repost?`: the URIs of the signed-in account's like and repost of the post (`{}` on a public view; written as no `viewer` member) |
| `ProfileViewer` | `muted`, `blockedBy`, `blocking?`, `following?`, `followedBy?` (record URIs); `Profile.viewer`, `{}` by default |
| `StrongRef` | `uri`, `cid`: a record by URI and content hash |
| `Posts`, `Call.getPosts uris` | `app.bsky.feed.getPosts`: up to `maxGetPosts` = 25 posts by URI |
| `Embed` | `images`, `external`, `record (Quote)`, `recordWithMedia Quote Media`, `other type` |
| `Quote` | `post QuotedPost`, `notFound uri`, `blocked uri`, `detached uri`, `other type` |
| `Profile`, `Image` (`thumb`, `fullsize`, `alt`, `aspect?`), `External` | |
| `X.ofJson`, `X.toJson` | every type above; decoders are total, ignore unknown fields, and read a malformed or unknown union member as `other "$type"` |
| `nsidGetTimeline`, `nsidGetAuthorFeed`, `pageParams limit cursor` | |

### Dates (`CairnAtproto.Datetime`)

`parseDatetime : String → Option Int`: an RFC 3339 date-time (`T`/`t`, `Z`/`z` or `±hh:mm`,
any fraction) as UTC milliseconds since the epoch, the fraction truncated; `none` if it isn't
one. `formatDatetime : Nat → String` writes milliseconds since the epoch as
`YYYY-MM-DDTHH:MM:SS.mmmZ` (JavaScript's `toISOString`), for a record's `createdAt` and
`updateSeen`. Until a `cairn_date` exists.

### The session machine (`CairnAtproto.Session`)

A pure state machine: `step : State → Input → State × List Out`.

| `Input` | |
|---|---|
| `signIn host identifier password` | from `launched` or signed out; otherwise `busy` |
| `resume host` | at launch: refresh the session the Keychain items hold |
| `call id c` | an XRPC `Call` (`Call.getTimeline`, `Call.getAuthorFeed`, `Call.getSession`, or any query or procedure) |
| `cancel ids` | the app no longer wants these calls: dropped in flight (request cancelled) or held, never answered |
| `signOut` | |
| `reply rid r` | the host's `Cairn.Reply` to request `rid` |

| `Out` | |
|---|---|
| `send rid kind r` | send Cairn request `r` as request `rid` (`kind`: `signIn`, `refresh`, `call ticket`) |
| `forget rid item` | delete Keychain item `item`: `Request.forgetSecret item` as request `rid` |
| `cancel rid` | request `rid` is no longer wanted: `Effect.cancelRequest rid` |
| `answer id a` | call `id` has ended: `reply r` (read it with `Outcome.ofReply`) or `signedOut` |
| `event e` | `signedIn a`, `refreshed a`, `signInFailed r`, `refreshFailed r`, `signedOut why`, `busy` |

Phases: `launched → (resume) refreshing → signedIn`, `signedOut/launched → (signIn) signingIn →
signedIn`, `signedIn → (ExpiredToken) refreshing → signedIn`, any `→ (signOut) signedOut`.
Calls go to the account's PDS (from the DID document), else the host signed in to.

- A call answered `ExpiredToken` on its first send starts one `refreshSession` (or joins the one
  in flight) and is held, as are calls made meanwhile. When the refresh succeeds every held call
  is sent again.
- A refresh that got no answer (network failure, timeout, 5xx, 429) answers the held calls with
  its failure and leaves the session as it was. Any other reply that isn't a session is a
  refusal: it forgets both items, answers the held calls `signedOut` and signs out.
- Signing out forgets both items and answers the held calls. A sign-in or refresh still in
  flight is abandoned: when its reply comes the items are forgotten again (it may have written
  new tokens), and `signIn` answers `busy` until then.

### Acting: record keys, writes and read-back (`CairnAtproto.Tid`, `.AtUri`, `.Lexicon.Repo`, `.Acts`)

For Sky's like, repost, follow and mute (cairn#249). Every call is a `Session.Call`, made with
`Session.Input.call id c` like `Call.getTimeline`; the session sends it to the account's PDS
with its access token, and answers `answer id a`.

```lean
-- A record key the client chooses: a TID, minted from the host's clock in microseconds.
let clock := TidClock.new 0                       -- keep it in the app's state
let some (tid, clock) := clock.mint nowMicros | …  -- strictly increasing: cairn_atproto^18
-- The write: a like of a post the app shows, at that key.
let w : PutRecord := { repo := account.did, rkey := tid.encode,
                       record := .likeOf post (formatDatetime nowMs) }
step s (.call 12 (Call.putRecord w))              -- POST com.atproto.repo.putRecord
-- Its answer:
match WriteOutcome.ofAnswer a with
| .acked => …                                     -- held by the server; w.uri is the like
| .refused status e reset => …                    -- not applied; o.describe now for words
| .lost why => step s (.call 13 (Call.getRecord w.uri))  -- unknown: read it back
| .notSent => …                                   -- not applied
-- The read-back's answer: ReadBack.ofAnswer a = .found view | .missing | .unsure
-- Unlike: Call.deleteRecord u, with u the like's AtUri (the post's viewer.like, AtUri.parse).
```

| | |
|---|---|
| `Tid` | `micros < 2^53`, `clock < 1024`; `encode` (13 chars of `234567abcdefghijklmnopqrstuvwxyz`, sorting as the number does), `Tid.decode`, `toNat` |
| `TidClock` | `new clockId`, `mint now : Option (Tid × TidClock)`: at `max now (last + 1)`, so strictly past the last key even when the clock stands still or steps back; `none` past 2^53 µs (year 2255) |
| `AtUri` | `repo`, `collection`, `rkey`; `toString` (`at://repo/collection/rkey`), `AtUri.parse` |
| `Record` | `like StrongRef createdAt`, `repost StrongRef createdAt`, `follow did createdAt`, `other type`; `likeOf post t`, `repostOf post t`, `followOf did t`, `collection`, `toJson`, total `ofJson` |
| `PutRecord` | `repo`, `rkey`, `record`; `uri : AtUri`, `toJson` (putRecord's body), `ofJson` |
| `RecordView` | `getRecord`'s answer: `uri`, `cid?`, `value : Record` |
| `ProfileDetail` | `getProfile`'s answer: `profile` (with `viewer`), `description?`, follower, follows and post counts |

| Call | Request | Read its answer with |
|---|---|---|
| `Call.putRecord w` | POST `com.atproto.repo.putRecord`, body `w.toJson` | `WriteOutcome.ofAnswer`; the body: `StrongRef.ofPutReply` |
| `Call.deleteRecord u` | POST `com.atproto.repo.deleteRecord` | `WriteOutcome.ofAnswer` |
| `Call.getRecord u` | GET `com.atproto.repo.getRecord?repo&collection&rkey` | `ReadBack.ofAnswer` |
| `Call.muteActor actor`, `Call.unmuteActor actor` | POST `app.bsky.graph.muteActor` / `unmuteActor` | `WriteOutcome.ofAnswer`; read back with `getProfile` (`viewer.muted`) |
| `Call.getProfile actor` | GET `app.bsky.actor.getProfile?actor` | `Outcome.ofReply ProfileDetail.ofJson` |
| `Call.getPosts uris` | GET `app.bsky.feed.getPosts?uris=…` (the first 25) | `Outcome.ofReply Posts.ofJson` |
| `Call.listNotifications limit cursor` | GET `app.bsky.notification.listNotifications` | `Outcome.ofReply NotificationPage.ofJson` |
| `Call.getUnreadCount` | GET `app.bsky.notification.getUnreadCount` | `Outcome.ofReply unreadCountOf` |
| `Call.updateSeen seenAt` | POST `app.bsky.notification.updateSeen` | `WriteOutcome.ofAnswer` |

**A write's reply** (`WriteOutcome.ofReply`, `ofAnswer`; `cairn_atproto^21`):

| Reply | Outcome | `applied` |
|---|---|---|
| 2xx | `acked` | `some true` |
| any other status below 500 (`RateLimitExceeded` with its `ratelimit-reset`, `InvalidRequest`, `InvalidSwap`, …) | `refused status error reset` | `some false` |
| 5xx, timeout, network failure, any other host failure | `lost why`: read it back before deciding; don't send blind | `none` |
| the host never sent it (Keychain item missing, denied), or the session answered `signedOut` | `notSent` | `some false` |

A write answered `ExpiredToken` never reaches the app: the session refreshes and sends it once
more (`cairn_atproto^12`, `^13`); the first was not applied (`^25`, assumed). `describe o now`
gives words for a status line ("rate limited, try again in 40 s").

**A read-back** (`ReadBack.ofReply`): `found view` on a 2xx with a record, `missing` on 400
`RecordNotFound` or 404, `unsure` on anything else (read again later). `getRecord` on the
account's own PDS reads every write it acknowledged (`^23`, assumed), where the AppView's views
(timeline, `getPosts`, `getProfile`) may lag.

**Viewer state.** A signed-in timeline's posts carry `viewer.like` and `viewer.repost` (the
account's records), and authors `viewer.muted`, `following`, … A post's counts include the
viewer's own like and repost exactly when `viewer` says so (`^24`, assumed), so a client shows
`likeCount - [viewer.like] + [shown liked]`.

### Notifications (`CairnAtproto.Lexicon.Notification`)

| | |
|---|---|
| `NotificationPage` | `notifications`, `cursor?` (none at the end), `seenAt?` |
| `Notification` | `uri`, `cid` (the record the author made), `author : Profile`, `reason`, `reasonSubject?` (the liked or reposted post), `text?` (a reply's, mention's or quote's), `isRead`, `indexedAt` |
| `NotificationReason` | `like`, `repost`, `follow`, `mention`, `reply`, `quote`, `other "<reason>"` (`starterpack-joined`, …) |
| `unreadCountOf`, `seenAtJson`, `seenAtOf` | `getUnreadCount`'s answer, `updateSeen`'s body |

### A paged list (`CairnAtproto.Paged`)

`Paged α`: a list the server pages by cursor, newest first, that the app shows and extends; the
home feed is `Paged FeedItem`, notifications `Paged Notification` (cairn#250, moved here from
Sky's `Feed`). Items are told apart by `Keyed.key` (a feed item: its post URI and reason; a
notification: its URI). It holds `items`, `cursor`, `atEnd`, and the `loadMore` (call id and
cursor) and `refresh` (call id) in flight.

```lean
-- Load more: ask from the cursor it holds; append the page if the list still holds it.
match f.beginLoadMore id with
| some (f, c) => step s (.call id (Call.listNotifications (some 30) (some c)))
| none => …                                 -- one in flight, empty, at the end
-- Refresh: ask for the head; withdraw the load-more it forgets (Input.cancel).
match f.beginRefresh id with
| some (f, withdraw) => …                    -- withdraw : Option Nat
| none => …                                 -- a refresh is in flight
-- Answers: `none` if the call failed; other calls' answers are ignored.
f.gotLoadMore id (page? : Option (Page α))   -- page from NotificationPage.page / FeedPage.page
f.gotRefresh id page?                       -- new items on top, or the list replaced
```

`content`, `canLoadMore`, `inFlight`, `appendPage`, `headPage`, `replaceBy` and `newOnTop` are
there too. Proved for every item type (`CairnAtproto.Proofs.Paged`, `^26`–`^29`): the list stays
a contiguous run of the server's list with no duplicates; a stale load-more page changes
nothing; the cursor is never lost; a refresh and a load-more answered in either order end the
same.

## What is proved

With no `sorry` and no axioms beyond `propext`, `Classical.choice` and `Quot.sound`
(`make audit`), every declaration replayed by the kernel (`make kernel`).

### Claims (`CairnAtproto.Claims`, `claims.lock`)

The claims are stated over a harness machine whose state is a `Session.Model` (the session and
the log of every step it took) and whose moves and `receive` feed it the app's inputs and the
host's replies. Each invariant's `holds` is `Ok m ∧ P m`, and `Ok.feed` (in
`CairnAtproto.Proofs.Session`) keeps `Ok` for every input, so each property holds after any
sequence of inputs from any app, not only the harness's.

| Id | Kind | Claim |
|---|---|---|
| `cairn_atproto^1`–`^4` | move | the app's inputs: sign in, resume, a call, sign out |
| `cairn_atproto^16` | move | cancel a call: afterwards no call with its id is in flight or held, and the phase is unchanged |
| `cairn_atproto^11` | invariant | at most one `refreshSession` in flight (`OneRefresh`) |
| `cairn_atproto^12` | invariant | every call is sent at most twice (`AtMostTwice`) |
| `cairn_atproto^13` | invariant | a call already sent is sent again only in the step a refresh in flight gets a 2xx session (`RetryAfterRefresh`) |
| `cairn_atproto^14` | invariant | signed out or signing in, no request carrying a Keychain secret is issued (`NoSecretSignedOut`) |
| `cairn_atproto^9` | invariant | a failed refresh answers every held call in that step; a refused one also forgets both items and answers them `signedOut`; calls are held only while a refresh is in flight (`RefusalEndsAll`) |
| `cairn_atproto^15` | assume | no Lean value holds a token. By construction (no type has a token field) and `SessionInfo.ofJson_replaceTokens` (the decoder reads the same account whatever `accessJwt` and `refreshJwt` hold); its check `atproto.no-token` is `make fake-fuzz` (below, "The fake PDS") |

The acting claims are in `CairnAtproto.ActClaims`, over a harness machine whose state is a
`TidClock` and the keys it minted; the others hold of every value, so they hold in every state.

| Id | Kind | Claim |
|---|---|---|
| `cairn_atproto^17` | move | mint a record key at a clock reading: a new key past every earlier one, or none |
| `cairn_atproto^18` | invariant | minted record keys strictly increase, as numbers and as text, whatever the clock reads (`Minted`) |
| `cairn_atproto^19` | invariant | a TID's text is 13 sortable base-32 chars and reads back as the TID (`TidText`) |
| `cairn_atproto^20` | invariant | the same write is the same `putRecord` request, and its body reads back as the write (`SameWrite`) |
| `cairn_atproto^21` | invariant | how a write's reply is read: acked exactly on 2xx, refused below 500, lost on 5xx/timeout/network, not sent otherwise (`WriteReading`) |
| `cairn_atproto^22` | assume | `putRecord` at a key already written with the same record, and `deleteRecord` of a missing record, change nothing (check `atproto.idempotent-writes`) |
| `cairn_atproto^23` | assume | `getRecord` on the account's PDS reads every write it acknowledged (check `atproto.read-your-writes`) |
| `cairn_atproto^24` | assume | a post's counts and viewer state are from one moment (check `atproto.count-viewer`) |
| `cairn_atproto^25` | assume | a write answered `ExpiredToken` was not applied (check `atproto.expired-not-applied`) |
| `cairn_atproto^26` | invariant | a paged list is a contiguous run of the server's list, with no duplicates (`Paged.Contiguous`) |
| `cairn_atproto^27` | invariant | a stale load-more page changes nothing (`gotLoadMore_stale`) |
| `cairn_atproto^28` | invariant | a paged list not at its end never loses its cursor (`CursorKept`) |
| `cairn_atproto^29` | invariant | a refresh and a load-more answered in either order end the same (`race`) |
| `cairn_atproto^30` | invariant | the acting decoders read back what their encoders write (`ReadsBack`) |
| `cairn_atproto^31` | invariant | the fake PDS's writes are idempotent, and getRecord reads the repo as it is now (`Fake.WritesHold`) |
| `cairn_atproto^32` | invariant | the fake's like and repost counts are its records', the viewer's own exactly when `viewer` says so (`Fake.CountsHold`) |
| `cairn_atproto^33` | invariant | the fake's notification pages are contiguous runs, newest first (`Fake.NoticesRun`) |

The checks of `^22`–`^25` run against the fake PDS in `make fake-fuzz` (below, "The fake PDS"),
which proves `^22`–`^24` of itself (`^31`–`^33`). Bluesky's own servers are another matter: all
four are still to be checked once against the real network with the installed app (cairn#258).

Retired in 0.2.0: ^5–^8 (their statements changed when requests became Cairn's `Request` and the
session gained `cancel`; the same claims are now ^11–^14) and ^10 (its text said the trusted-base
fuzz checks it; it is now ^15, checked by `make fake-fuzz`).

The bookkeeping invariant `Inv` behind ^11–^13 relates the state to the log: request ids are
fresh, tickets are distinct, each pending call has been sent `tries` times (a held one at most
once), every refresh in flight is the phase's or abandoned, and at most one request is abandoned.
`Inv.of_step` proves every step keeps it.

### Decoders

```lean
-- CairnAtproto.Proofs.RoundTrip: every encoder's output decodes to the value.
theorem FeedPage.ofJson_toJson (p : FeedPage) : FeedPage.ofJson p.toJson = some p
theorem SessionInfo.ofJson_toJson (s : SessionInfo) : SessionInfo.ofJson s.toJson = some s
theorem XrpcError.ofJson_toJson (e : XrpcError) (h : e.name.Canonical) :
    XrpcError.ofJson e.toJson = e
-- (and Profile, Image, External, QuotedPost, Quote, Media, Embed, Post, ReplyRef, ReplyCtx,
-- Reason, FeedItem, StrongRef, ProfileViewer, PostViewer, PostReplyRef, Posts, ProfileDetail,
-- Record, PutRecord, RecordView, Notification, NotificationPage; CairnAtproto.Proofs.Acts)
-- CairnAtproto.Proofs.Tid
theorem Tid.decode_encode (t : Tid) : Tid.decode t.encode = some t
theorem TidClock.mint_increasing (h : g.mint now = some (t, g')) (l : Nat) (hl : g.last = some l) :
    l < t.micros
theorem SessionInfo.ofJson_replaceTokens (v : String → Json) (kvs : List (String × Json)) :
    SessionInfo.ofJson (.obj (kvs.map (replaceTokens v))) = SessionInfo.ofJson (.obj kvs)

-- CairnAtprotoProofs.Text: through text, with cairn_json's round trip.
theorem FeedPage.decode_encode (p : FeedPage) (slash : Bool) :
    (decode (encode p.toJson slash)).bind FeedPage.ofJson = some p
theorem SessionInfo.decode_encode (s : SessionInfo) (slash : Bool) :
    (decode (encode s.toJson slash)).bind SessionInfo.ofJson = some s
theorem XrpcError.decode_encode (e : XrpcError) (h : e.name.Canonical) (slash : Bool) :
    (decode (encode e.toJson slash)).map XrpcError.ofJson = some e
-- and NotificationPage, Posts, ProfileDetail, RecordView; a putRecord call's body reads back
-- as its write (Session.Call.putRecordOf_putRecord).
```

Decoders are total by construction: every one is a structurally recursive Lean function (no
`partial`, checked by `make lint` and the kernel). `Canonical` excludes `other "ExpiredToken"`
and the like, which decode as the named constructor.

### Fixtures

`make fixtures` decodes every file in `fixtures/` with `lake exe fixtures`, checks the summary
against `fixtures/expected.txt`, and checks every date it parsed against Python's calendar
(`tools/check-fixtures.py`).

- `fixtures/public/`: `app.bsky.feed.getAuthorFeed` for `bsky.app` from
  `public.api.bsky.app`, two pages, recorded with no authentication; and its error for an actor
  that doesn't exist; `app.bsky.actor.getProfile` and `app.bsky.feed.getPosts` (three posts)
  for `bsky.app`, and `getProfile`'s error for an account that doesn't exist.
- `fixtures/synthesized/`: a `getTimeline` page with every embed kind, quote kind, reason and
  reply kind; the last page; `createSession`, `refreshSession` and `getSession` replies with
  the tokens blank, as the host hands them to Lean; and the four named errors.
- `fixtures/synthesized/`, for acting: a timeline, `getPosts` and `getProfile` with the
  viewer's state (liked, reposted, muted, following, blocking); `listNotifications` with every
  reason and one unknown, and its last page; `getUnreadCount`; `getRecord` of a like, a follow
  and a post; `putRecord`'s reply; 400 `RecordNotFound` and `InvalidSwap`; and a timeline page
  from the fake PDS with replies to posts, deleted posts and blocked posts.

Build-time tests (`#guard`, in `CairnAtprotoTests`) cover URLs, errors, `Outcome.ofReply`, dates
and session scenarios; TIDs (a known one, minting with the clock still or stepping back), AT
URIs, every acting call's URL and body, `WriteOutcome.ofReply`, `ReadBack.ofReply`,
notification reasons, `Paged` runs, and the fake's replies.

## The fake PDS

Two fakes of a PDS with the same behaviour, so nothing needs the real network to be tested
(cairn#208): a Lean model, `CairnAtproto.Fake`, and a local server, `tools/fake-pds/` (Bun).
`make fake-pds-replay` replays random sequences of calls against both and compares every answer
(status, error, body with its cursor and page items, rate-limit headers, delays, timeouts, image
sizes). Neither holds a real credential or talks to the network.

| | |
|---|---|
| Timeline | grows only at its head: post `k` (from the oldest) is `postAt cfg k`, a function of the seed and `k`; 1–3 posts arrive after an XRPC request with chance `1/arrival`, or on `POST /control/post?n=`. About one post in four is a reply (`replyTarget`): to an older post (with its thread's root, and the grandparent's author when the parent is itself a reply), to a deleted post (`notFoundPost`) or to a blocked one (`blockedPost`); the record carries `reply` too. About one in four is the tester's own (`isMine`); some quote an older post or mention the tester |
| `getTimeline` | `limit` 1–100 (default 50), newest first; `cursor` is opaque (`<createdAt>::<cid>` of the page's oldest post), absent at the end, and stays valid as posts arrive; a bad one is 400 `InvalidRequest`. Leaves out posts by muted accounts and reposts by them |
| `createSession` | one identifier and app password, from the seed (`Config.identifier`, `Config.password`); otherwise 401 `AuthenticationRequired` |
| Tokens | a generation per sign-in or refresh. The access token serves 1 to `life` calls, then 400 `ExpiredToken`; `refreshSession` rotates both and refuses the old refresh token (400 `InvalidToken`). A token is a marker, `fakepds-token.<kind>.<gen>.<nonce>` |
| The tester's repo | `putRecord` of a like, repost or follow (`repo` the tester's DID, any valid record key): 200 `{uri, cid}`; the same record at the same key again changes nothing and answers the same. Another repo, a bad key or another collection: 400 `InvalidRequest`. `deleteRecord`: 200, there or not. `getRecord`: the record, or 400 `RecordNotFound`; it reads the repo as it is now, never lagging |
| Mutes and profiles | `muteActor`, `unmuteActor` (handle or DID of one of the other accounts; not the tester): 200, and the timeline leaves their posts out. `getProfile`: `ProfileDetail` with the viewer's `muted` and `following` (the follow record's URI) |
| Viewer state | posts in `getTimeline` and `getPosts` (≤ 25 `uris`) carry `likeCount`/`repostCount` (seeded counts plus every like and repost record) and `viewer.like`/`viewer.repost` (the tester's record's URI), all from one moment |
| Other accounts | after each XRPC request, with chance `1/act`, one of the six other accounts likes or reposts a post or follows the tester, or takes back what it did; or on `POST /control/act` |
| The AppView's lag | each change (a write, a mute, another account's act, a post that notifies) is seen by the AppView 0 to `lag` XRPC requests later, never before an earlier change: views (timeline, `getPosts`, `getProfile`, notifications) show a prefix of the changes. `POST /control/lag?n=` sets it; `/control/catchup` shows everything now |
| Notifications | `listNotifications` (`limit` 1–100, default 50; newest first; `cursor` opaque, absent at the end): likes, reposts and quotes of the tester's posts, replies to them, mentions, follows. `isRead` is by `seenAt`. `getUnreadCount`; `updateSeen` (`seenAt` a datetime, else 400) |
| Faults | `POST /control/fail?n=&kind=500\|503\|429\|timeout\|400\|lost-after` (the next `n` calls: `400` is refused before anything is applied; `lost-after` applies the call and never replies), `/control/slow?ms=`, `/control/expire`, `/control/revoke`; `GET /control/state` |
| Images | `GET /img/<w>x<h>/<name>.png`: a PNG of that size (avatars and embeds point here) |
| Other methods | 501 `MethodNotImplemented` (`getAuthorFeed` too, for now); a method with the wrong HTTP verb is 400 before its token is checked |

The control calls, all on the server's origin:

| Call | Does |
|---|---|
| `POST /control/post?n=3` | `n` posts arrive at the head (with their notifications) |
| `POST /control/act?kind=like&actor=2&post=17` | account `actor` (0–5: ada, zoe, lei, sam, noor, kit) does `kind` (`like`, `repost`, `follow`) on post `post`, by default the tester's newest; again takes it back |
| `POST /control/lag?n=5` | the AppView sees a change 0 to `n` requests after it, from now on |
| `POST /control/catchup` | the AppView sees every change now |
| `POST /control/fail?n=2&kind=lost-after` | the next `n` calls fail (above, "Faults") |
| `POST /control/slow?ms=800` | every XRPC reply waits `ms` |
| `POST /control/expire`, `/control/revoke` | the access token expires; the session ends |
| `GET /control/state` | counts: posts, requests, the log and how much of it the AppView sees, the repo's record URIs, mutes, others' likes, reposts and follows, `seenAt` |

The server's flags: `--port 2583 --seed N --base 40 --arrival 3 --life 6 --act 4 --lag 2
--quiet` (`--act 0`: nobody else acts on their own; `--lag 0`: no lag).

What is proved (`CairnAtproto.Proofs.Fake`): a request keeps the configuration and never
shortens the timeline (`Server.handle_cfg`, `Server.handle_length`), so the timeline after it
extends the one before at its head (`Server.handle_timeline`, with `timeline_extends`); a page is
a contiguous run of the timeline (`page_feed`, `page_head`), and so is a page with muted accounts
left out (`pageWhere_run`). Writes are idempotent, `getRecord` reads them, a missing delete
changes nothing (`WritesHold`, `^31`); a post's counts are its records' and its viewer state is
from the same facts (`CountsHold`, `^32`); a notification page is a contiguous run, newest first
(`NoticesRun`, `^33`).

**In Lean.** `Fake.Server.handle` answers a request; `Fake.World` adds the host: the Keychain
(which token each item holds, `World.generation`) and cairn#205's capture (a 2xx JSON object, all
or nothing, the fields blanked before Lean sees the body), so `World.send` takes the session
machine's `Cairn.Request` and gives the `Cairn.Reply` Lean receives. `lake exe fake-pds-model` is the
model over JSON lines, for the replay. The server keeps one log of changes (`Server.log`); the
repo as it is (`Server.now`) is all of it, what the AppView shows (`Server.seen`) is the prefix it
has caught up with.

**In `cairn fuzz`, stateless.** `Fake.replies cfg hooks` has the type of `Cairn.Fuzz.Custom.replies`:

```lean
def fuzz : Cairn.Fuzz.Custom State where
  replies := CairnAtproto.Fake.replies {} { phase := fun s => some s.session.phase }
```

Cairn's hook keeps no state between replies, so each reply is what `Server.handle` answers in a
state drawn at random that fits the request: the timeline as it stands at request `id`
(`Fake.timeline cfg (cfg.base + arrivedBefore cfg (id + 1))`, growing at the head as ids grow,
so a claim can be stated against it), the access token expired with chance `1/life`, a refresh
refused one time in ten, a missing Keychain item (`failed notFound`) by the session's phase, and a
500, 503, 429, timeout or network failure one time in eight. The request says which token it
carries (its `secret`'s Keychain item, none without one) and what the host captures (its
`capture`); `Hooks.capture` overrides that only to check that a leak is caught, and
`replyHasMarker` finds a token that wasn't captured. Images on the fake are answered with their
size.

**In `cairn fuzz`, as a server** (cairn#260's `Custom.server`, in cairn 0.5.0). The fake has the
pieces of a `Cairn.Fuzz.Server World`, whose world is the whole `Fake.World` (the PDS and the
host's Keychain), so writes, likes and mutes persist through a sequence: `Fake.worldGen cfg`
(a configuration drawn per sequence: seed, base, arrival, life, act, lag), `Fake.handles` (XRPC
requests; images stay with `replies`), `Fake.serve` (`World.send`), `Fake.tick` (posts arrive,
another account acts, the AppView catches up, the token expires) and `World.describe`. The
accessors for an app's checks read the repo as it is (what the AppView shows once it catches
up): `World.likedBy w uri`, `World.repostedBy w uri`, `World.likeCount w uri` (seeded likes plus
like records), `World.muted w did`, `World.seenAt w`.

`Fake.server cfg checks drained` puts them together (it needs cairn 0.5.0, which this package
requires):

```lean
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
```

An app plugs it in, keeping `replies` for images (the check here is an example, for an app
whose state lists posts with a `liked` flag):

```lean
def fuzz : Cairn.Fuzz.Custom State where
  replies := CairnAtproto.Fake.replies {} { phase := fun s => some s.session.phase }
  server := some (CairnAtproto.Fake.server {}
    (drained := [(52, fun s w => s.posts.all fun p => p.liked == w.likedBy p.uri)]))
```

`retransmit` stays off: a retransmitted `refreshSession` is refused after the first rotated the
tokens, a refusal that did something.

The world starts with an empty Keychain, and the identifier and password the fake accepts come
from the seed `worldGen` draws, which the app can't know. An app that opens a saved session at
launch, as Sky does, starts from a world that holds one: `World.saved` sends the session's own
`createSession` with the world's identifier and password through the host, which captures the
tokens (`{ Fake.server {} … with init := Fake.World.saved <$> Fake.worldGen {} }`).

**FakeApp** (`lean/FakeApp.lean`, `make fuzz-app`, in `make check`; `cairn fuzz FakeApp` does the
same): a small app on the session machine, run under `cairn fuzz` through Cairn's runtime with
`Fake.server` as its server. It opens the saved session, loads the timeline, likes posts and
signs out; its invariant `fake_app^6` (a like the server acknowledged shows liked) carries the
server check that the tester's repo holds every acknowledged like, after every step and once
every reply is in, while replies fail before the server acts or are lost after, tokens expire
and rotate, and other accounts act. Its claims are in their own scope, `fake_app`, unpublished;
`lake exe fuzz` is the package's fuzz executable (`Claims`, the session machine's harness, runs
at the model level).

**`atproto.no-token`** (`make fake-fuzz`, in `make check`; claim `^15`'s check): the session
machine against `Fake.World` in random sequences (sign-ins with right and wrong passwords,
resumes, calls, writes, mutes, reads, cancels, sign-outs; replies in any order, lost after the
server handled them, or failed before it; posts arriving, other accounts acting, the AppView
lagging, tokens expiring and revoked, faults), searching after every step the reply handed to
Lean, the session's state and everything it put out for a token marker. It then runs the same
sequences with the host's capture off, which must find markers. It also decodes every page and
checks that no cancelled call is answered. The report is `build/fake-fuzz.json`.

**The assumptions' checks**, in the same run (each must see cases and no violation; the report's
`assumptions`):

| Check | Claim | Against the fake |
|---|---|---|
| `atproto.idempotent-writes` | `^22` | every 2xx write (put, delete, mute, unmute, updateSeen) sent again, on a copy of the world, leaves the repo, mutes and `seenAt` as they were |
| `atproto.read-your-writes` | `^23` | after every 2xx `putRecord`, `getRecord` (on a copy) answers the record written; after every 2xx `deleteRecord`, `RecordNotFound`; whatever the lag |
| `atproto.count-viewer` | `^24` | every post view the app is handed (timeline, `getPosts`) has the counts of the moment it was served, the tester's like (repost) counted exactly when `viewer.like` (`.repost`) is set |
| `atproto.expired-not-applied` | `^25` | every write answered 400 `ExpiredToken` changed nothing |

These say the fake behaves as the client assumes Bluesky does. That Bluesky does is cairn#258's:
the same four checks, once, against the real network with the installed app.

### Running Sky against the fake PDS

```sh
make fake-pds                         # = bun tools/fake-pds/server.ts (port 2583; --port, --seed, --act, --lag)
# fake-pds listening on http://127.0.0.1:2583
# seed 1234…
# identifier tester-abcd.fake.test
# app password abcd-efgh-ijkl-mnop
defaults write <Sky's bundle id> service http://127.0.0.1:2583
```

Sky reads `service` with `readDefault`; sign in on its sign-in screen with the printed identifier
and app password. The control calls drive it from outside, for example:

```sh
curl -X POST 'http://127.0.0.1:2583/control/fail?n=3&kind=timeout'   # the next 3 calls time out
curl -X POST 'http://127.0.0.1:2583/control/act?kind=like&actor=1'   # zoe likes your newest post
curl -X POST 'http://127.0.0.1:2583/control/lag?n=8'                 # the AppView falls behind
curl -X POST 'http://127.0.0.1:2583/control/fail?n=1&kind=lost-after' # the next write applies, its reply is lost
curl -X POST 'http://127.0.0.1:2583/control/catchup'
curl 'http://127.0.0.1:2583/control/state'
```

Sky's likes, reposts, follows and mutes write to the tester's repo there; notifications come
from the tester's posts being liked, reposted, quoted and replied to. `defaults delete <Sky's bundle id> service` and
the same build talks to the real network again. Stop the server with Ctrl-C.

**Real credentials go only into the running app's sign-in screen**: never into a file, fixture,
test, log, script or command line, in this repository or any other. The fake's identifier,
password and tokens are generated and fake; its log shows paths and statuses, never a token or a
`createSession` body.

## 0.3.0

26 October 2026. For Sky's M5 (cairn#249, cairn#250, cairn#236), on Cairn 0.5.0.

- **Cairn ^0.5.0** (was ^0.3.0). An app on 0.3.0 moves to Cairn 0.5.0 too (Cairn's release
  notes, "Upgrading to v0.5.0": every app links Lean's `libStd`, frames v13).
- **`Fake.server`**: the fake PDS as a `cairn fuzz` server (cairn#260), its world the whole
  `Fake.World`, and `Fake.World.saved`, a world with a signed-in session in its Keychain for an
  app that resumes at launch; FakeApp runs it under `cairn fuzz` (`make fuzz-app`, above).

- **Record keys**: `Tid`, `TidClock.mint` (strictly increasing, `^17`–`^19`), `AtUri`.
- **Writes**: `Record` (like, repost, follow), `PutRecord`, `Call.putRecord`, `deleteRecord`,
  `getRecord`, `muteActor`, `unmuteActor`; `WriteOutcome` (how a write's reply is read, `^21`)
  and `ReadBack`; the same write is the same request (`^20`); assumptions about Bluesky's
  servers as `assume` claims `^22`–`^25`.
- **Viewer state**: `Post.viewer`, `Profile.viewer`, `Post.reply` (the record's), `getProfile`
  (`ProfileDetail`), `getPosts` (`Posts`).
- **Notifications**: `listNotifications`, `getUnreadCount`, `updateSeen`.
- **`Paged α`**, moved from Sky's `Feed` with its proofs (`^26`–`^29`), plus `beginLoadMore`,
  `beginRefresh`, `canLoadMore`, `inFlight`.
- **Fake PDS**: replies in the timeline, to older posts, deleted posts and blocked posts
  (cairn#236).
- **Fake PDS acts** (cairn#251), the same in the Lean model and the Bun server: the tester's
  repo (`putRecord`, `deleteRecord`, `getRecord` of likes, reposts and follows), `muteActor`,
  `unmuteActor`, `getProfile`, `getPosts`, with viewer state on posts and profiles and muted
  accounts left out of the timeline; other accounts acting (`--act`, `/control/act`); an AppView
  lagging 0 to `lag` requests (`--lag`, `/control/lag`, `/control/catchup`), `getRecord` never;
  notifications (`listNotifications`, `getUnreadCount`, `updateSeen`); write faults `400` and
  `lost-after`. `make fake-fuzz` writes and runs the checks of `^22`–`^25`; claims `^31`–`^33`
  prove the fake's writes, counts and notification pages. The pieces of a `cairn fuzz` server
  (`Fake.worldGen`, `handles`, `serve`, `tick`, `World.likedBy`, `likeCount`, `muted`,
  `seenAt`, `describe`).
- `formatDatetime`.
- Upgrading: `Profile` and `Post` gained fields (`viewer`; `reply`, `viewer`), so anonymous
  constructors (`⟨…⟩`) and `obtain` patterns on them need the new fields; named-field
  construction is unchanged.

## Cairn 0.3.0

Since 0.2.0 this package is on Cairn 0.3.0 and its requests are Cairn's `Request.http`: the
session's `Out.send` carries the request the app sends as it is, with the Keychain secret,
captures and `redact` of cairn#205 and cairn#206. Upgrading from 0.1.x: `Http`, `KeychainSecret`
and `Method` are gone (read a request with `urlOf`, `itemOf`, `captureOf`, …); send
`Out.forget rid item` as `Request.forgetSecret item` and the new `Out.cancel rid` as
`Effect.cancelRequest rid`; cancel calls with `Input.cancel ids` instead of editing the state.

## Building

`make build`, `make check` (lint, build, axiom audit, ledger, kernel replay, fixtures, the
no-token fuzz and the fake PDS replay; the replay needs [Bun](https://bun.sh)).
`lake update` needs `RESERVOIR_API_URL=https://cairn.registry.nexthub.sh/api/v1` (the Makefile
sets it). CI runs `make check` on Ubuntu against the registry.
