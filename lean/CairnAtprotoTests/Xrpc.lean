import CairnAtproto

open CairnJson CairnAtproto

/-! URLs, errors, headers, dates. -/

-- URLs
#guard xrpcUrl "https://bsky.social/" "app.bsky.feed.getTimeline" [] ==
  "https://bsky.social/xrpc/app.bsky.feed.getTimeline"
#guard xrpcUrl "https://pds.example.com//" "app.bsky.feed.getTimeline"
    [("limit", "50"), ("cursor", "2026-10-01T12:00:00.000Z::bafy 1/é")] ==
  "https://pds.example.com/xrpc/app.bsky.feed.getTimeline?limit=50&cursor=2026-10-01T12%3A00%3A00.000Z%3A%3Abafy%201%2F%C3%A9"
#guard methodOf (query "https://h" "a.b.c") == "GET" && secretOf (query "https://h" "a.b.c") == none
#guard (createSession "https://bsky.social" "alice.test" "pw").redact
#guard bodyOf (createSession "https://bsky.social" "alice.test" "pw") ==
  "{\"identifier\":\"alice.test\",\"password\":\"pw\"}"
#guard captureOf (createSession "https://bsky.social" "a" "b") == [("accessJwt", "access"), ("refreshJwt", "refresh")]
#guard secretOf (createSession "https://bsky.social" "a" "b") == none
#guard secretOf (refreshSession "https://bsky.social") == some (Cairn.Secret.bearer "refresh")
#guard itemOf (refreshSession "https://bsky.social") == some "refresh"
#guard itemOf (getSession "https://bsky.social") == some "access"
#guard bodyOf (refreshSession "https://bsky.social") == "" && !(refreshSession "https://x").redact
-- What Cairn's frame dump prints for the sign-in: its size, not the password.
#guard !(reprStr (createSession "https://bsky.social" "alice.test" "pw-planted")).contains "pw-planted"

-- Errors
#guard (XrpcError.ofBody "{\"error\":\"ExpiredToken\",\"message\":\"Token has expired\"}".toUTF8) ==
  { name := .expiredToken, message := some "Token has expired" }
#guard (XrpcError.ofBody "{\"error\":\"InvalidRequest\"}".toUTF8).name == .other "InvalidRequest"
#guard (XrpcError.ofBody "<html>bad gateway</html>".toUTF8) == { name := .other "" }
#guard (XrpcError.ofBody ByteArray.empty).name == .other ""
#guard ["ExpiredToken", "InvalidToken", "AuthRequired", "RateLimitExceeded", "Nope", ""].all
  fun s => (ErrorName.ofString s).toString == s

-- Headers
#guard ratelimitReset [("Content-Type", "x"), ("RateLimit-Reset", " 1761400000 ")] == some 1761400000
#guard ratelimitReset [("ratelimit-reset", "soon")] == none
#guard ratelimitReset [] == none

-- Outcomes
#guard match Outcome.ofReply FeedPage.ofJson (.http 200 [] "{\"feed\":[]}".toUTF8) with
  | .ok p => p.feed.isEmpty && p.cursor.isNone | _ => false
#guard match Outcome.ofReply FeedPage.ofJson (.http 200 [] "{\"feed\":[{}]}".toUTF8) with
  | .malformed 200 => true | _ => false
#guard match Outcome.ofReply FeedPage.ofJson
    (.http 429 [("ratelimit-reset", "99")] "{\"error\":\"RateLimitExceeded\"}".toUTF8) with
  | .error 429 e (some 99) => e.name == .rateLimitExceeded | _ => false
#guard match Outcome.ofReply FeedPage.ofJson (.failed .network "offline") with
  | .failed .network _ => true | _ => false

-- Dates
#guard parseDatetime "1970-01-01T00:00:00Z" == some 0
#guard parseDatetime "1970-01-01T00:00:00.001Z" == some 1
#guard parseDatetime "2026-10-24T14:56:12.679Z" == some 1792853772679
#guard parseDatetime "2026-10-24T14:56:12.679999999Z" == some 1792853772679
#guard parseDatetime "2026-10-24T16:56:12.679+02:00" == some 1792853772679
#guard parseDatetime "2026-10-24t14:56:12z" == some 1792853772000
#guard parseDatetime "1969-12-31T23:59:59.999Z" == some (-1)
#guard parseDatetime "2024-02-29T00:00:00Z" == some 1709164800000
#guard parseDatetime "2016-12-31T23:59:60Z" == parseDatetime "2017-01-01T00:00:00Z"
#guard (parseDatetime "2023-02-29T00:00:00Z").isNone
#guard (parseDatetime "2026-10-24T24:00:00Z").isNone
#guard (parseDatetime "2026-10-24T14:56:12").isNone
#guard (parseDatetime "2026-10-24T14:56:12.Z").isNone
#guard (parseDatetime "2026-10-24 14:56:12Z").isNone
#guard (parseDatetime "2026-13-01T00:00:00Z").isNone
#guard (parseDatetime "").isNone
