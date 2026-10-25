# cairn_atproto

The AT Protocol (Bluesky) for [Cairn](https://github.com/iamnbutler/cairn) apps, in pure Lean:
XRPC requests and errors, lexicon types and decoders (on
[cairn_json](https://github.com/iamnbutler/cairn_json)), RFC 3339 dates, and a session machine
with proofs. Registry package `cairn_atproto`, Lean library `CairnAtproto`, claim scope
`cairn_atproto`. No Swift, no host code, no `@[extern]`.

**Tokens never reach Lean.** Sign-in and refresh replies have their `accessJwt` and
`refreshJwt` captured by the host into the Keychain items `access` and `refresh` (cairn#205), and
calls name the item that authorises them. No type here has a field for a token, and this
repository holds no credentials, tokens or private timelines: fixtures are recorded *public*
responses or synthesized.

```lean
-- lean/lakefile.lean, after `cairn add cairn_atproto`
require "iamnbutler" / "cairn_atproto" @ "^0.1.0"

import CairnAtproto
open CairnAtproto CairnAtproto.Session

-- A public feed, no session: GET https://public.api.bsky.app/xrpc/app.bsky.feed.getAuthorFeed?actor=bsky.app&limit=30
query "https://public.api.bsky.app" nsidGetAuthorFeed (("actor", "bsky.app") :: pageParams (some 30) none)

-- Its reply, read: .ok page, .error status e reset, .malformed status, .failed fault msg
Outcome.ofReply FeedPage.ofJson reply

-- The session: feed it the app's inputs and the host's replies; send what it says.
let (s, outs) := step init (.signIn "https://bsky.social" "alice.example.com" appPassword)
-- outs = [.send 0 .signIn (createSession …)]   (capture both tokens; the body is `redact`)
let (s, outs) := step s (.reply 0 reply)        -- [.event (.signedIn account)]
let (s, outs) := step s (.call 7 (Call.getTimeline (some 50)))
-- [.send 1 (.call 0) { url := "<pds>/xrpc/app.bsky.feed.getTimeline?limit=50", secret := access, … }]
```

## What's in it

### XRPC (`CairnAtproto.Xrpc`)

| | |
|---|---|
| `Http` | a request in the shape cairn#205 gives `Request.http`: `method`, `url`, `headers`, `body`, `timeoutMs`, `secret : Option KeychainSecret`, `capture : List (field × item)`, and `redact` (the body holds a password) |
| `KeychainSecret` | `header: scheme ++ <value of Keychain item account>`; by default `Authorization: Bearer …` |
| `accessItem`, `refreshItem` | `"access"`, `"refresh"` |
| `query service nsid params secret` | GET `service/xrpc/nsid?params` |
| `procedure service nsid body secret capture redact` | POST with a JSON body |
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
| `Post` | `uri`, `cid`, `author : Profile`, record `text` and `createdAt`, `embed?`, reply/repost/like/quote counts, `indexedAt` |
| `Embed` | `images`, `external`, `record (Quote)`, `recordWithMedia Quote Media`, `other type` |
| `Quote` | `post QuotedPost`, `notFound uri`, `blocked uri`, `detached uri`, `other type` |
| `Profile`, `Image` (`thumb`, `fullsize`, `alt`, `aspect?`), `External` | |
| `X.ofJson`, `X.toJson` | every type above; decoders are total, ignore unknown fields, and read a malformed or unknown union member as `other "$type"` |
| `nsidGetTimeline`, `nsidGetAuthorFeed`, `pageParams limit cursor` | |

### Dates (`CairnAtproto.Datetime`)

`parseDatetime : String → Option Int`: an RFC 3339 date-time (`T`/`t`, `Z`/`z` or `±hh:mm`,
any fraction) as UTC milliseconds since the epoch, the fraction truncated; `none` if it isn't
one. Until a `cairn_date` exists.

### The session machine (`CairnAtproto.Session`)

A pure state machine: `step : State → Input → State × List Out`.

| `Input` | |
|---|---|
| `signIn host identifier password` | from `launched` or signed out; otherwise `busy` |
| `resume host` | at launch: refresh the session the Keychain items hold |
| `call id c` | an XRPC `Call` (`Call.getTimeline`, `Call.getAuthorFeed`, `Call.getSession`, or any query or procedure) |
| `signOut` | |
| `reply rid r` | the host's `Cairn.Reply` to request `rid` |

| `Out` | |
|---|---|
| `send rid kind http` | send `http` as request `rid` (`kind`: `signIn`, `refresh`, `call ticket`) |
| `forget rid item` | delete Keychain item `item` (cairn#205's `Request.forgetSecret`) |
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
| `cairn_atproto^5` | invariant | at most one `refreshSession` in flight (`OneRefresh`) |
| `cairn_atproto^6` | invariant | every call is sent at most twice (`AtMostTwice`) |
| `cairn_atproto^7` | invariant | a call already sent is sent again only in the step a refresh in flight gets a 2xx session (`RetryAfterRefresh`) |
| `cairn_atproto^8` | invariant | signed out or signing in, no request carrying a Keychain secret is issued (`NoSecretSignedOut`) |
| `cairn_atproto^9` | invariant | a failed refresh answers every held call in that step; a refused one also forgets both items and answers them `signedOut`; calls are held only while a refresh is in flight (`RefusalEndsAll`) |
| `cairn_atproto^10` | assume | no Lean value holds a token. By construction (no type has a token field) and `SessionInfo.ofJson_replaceTokens` (the decoder reads the same account whatever `accessJwt` and `refreshJwt` hold); check `atproto.no-token` is for cairn#208's fuzz |

The bookkeeping invariant `Inv` behind ^5–^7 relates the state to the log: request ids are
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
-- Reason, FeedItem)
theorem SessionInfo.ofJson_replaceTokens (v : String → Json) (kvs : List (String × Json)) :
    SessionInfo.ofJson (.obj (kvs.map (replaceTokens v))) = SessionInfo.ofJson (.obj kvs)

-- CairnAtprotoProofs.Text: through text, with cairn_json's round trip.
theorem FeedPage.decode_encode (p : FeedPage) (slash : Bool) :
    (decode (encode p.toJson slash)).bind FeedPage.ofJson = some p
theorem SessionInfo.decode_encode (s : SessionInfo) (slash : Bool) :
    (decode (encode s.toJson slash)).bind SessionInfo.ofJson = some s
theorem XrpcError.decode_encode (e : XrpcError) (h : e.name.Canonical) (slash : Bool) :
    (decode (encode e.toJson slash)).map XrpcError.ofJson = some e
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
  that doesn't exist.
- `fixtures/synthesized/`: a `getTimeline` page with every embed kind, quote kind, reason and
  reply kind; the last page; `createSession`, `refreshSession` and `getSession` replies with
  the tokens blank, as the host hands them to Lean; and the four named errors.

Build-time tests (`#guard`, in `CairnAtprotoTests`) cover URLs, errors, `Outcome.ofReply`, dates
and session scenarios.

## cairn#205

This release depends on Cairn 0.2.5, whose `Request.http` has no secrets, so `Http` is this
package's own, in the shape cairn#205 gives `Request.http` in Cairn 0.3.0: `secret` is
`some (Secret.bearer item)`, `capture` is the same list, and `Out.forget` is
`Request.forgetSecret item`. `redact` has no counterpart yet; until it does, the app must keep
`createSession`'s body out of logs. A later release maps `Http` to `Request` once Cairn 0.3.0 is
on the registry.

## Building

`make build`, `make check` (lint, build, axiom audit, ledger, kernel replay, fixtures).
`lake update` needs `RESERVOIR_API_URL=https://cairn.registry.nexthub.sh/api/v1` (the Makefile
sets it). CI runs `make check` on Ubuntu against the registry.
