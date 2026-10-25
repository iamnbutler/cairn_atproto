module

public import Cairn.Effects
public import CairnAtproto.Json

/-! # XRPC

Requests to an AT Protocol service (`<service>/xrpc/<nsid>`) and the errors it answers.

* `Http`: a request as cairn#205's `Request.http` carries it: method, URL, headers, body and
  timeout, plus the Keychain item its `Authorization` header comes from (`secret`), the reply
  fields the host captures into Keychain items and blanks (`capture`), and whether the body
  must stay out of every dump and log (`redact`). Lean names the items; it never holds their
  values.
* `query` (GET, parameters in the URL) and `procedure` (POST, a JSON body) build one.
* `XrpcError`: an error body, `{"error": …, "message": …}`, decoded to a closed name.
* `ratelimitReset`: the `ratelimit-reset` header, seconds since the epoch. -/

@[expose] public section

namespace CairnAtproto
open CairnJson

/-- The Keychain item names the session uses (cairn#205: generic password items of the app). -/
def accessItem : String := "access"
def refreshItem : String := "refresh"

/-- A header whose value the host reads from a Keychain item when it sends the request:
`header: scheme ++ <item's value>`. cairn#205's `Secret` with source `keychain account`. -/
structure KeychainSecret where
  account : String
  header : String := "Authorization"
  scheme : String := "Bearer "
deriving Repr, DecidableEq, Inhabited

inductive Method where
  | get | post
deriving Repr, DecidableEq, Inhabited

def Method.name : Method → String
  | .get => "GET"
  | .post => "POST"

/-- An HTTP request in the shape cairn#205 gives `Request.http`. -/
structure Http where
  method : Method
  url : String
  headers : List (String × String) := []
  /-- UTF-8 text; empty for a query. -/
  body : String := ""
  timeoutMs : Nat := 30000
  /-- The `Authorization` header's item, if any. -/
  secret : Option KeychainSecret := none
  /-- For a 2xx JSON reply: `(field, item)` pairs the host writes to Keychain items and blanks
  to `""` before Lean sees the body. All or nothing. -/
  capture : List (String × String) := []
  /-- The body holds a password: no dump, log or frame shows it. -/
  redact : Bool := false
deriving Repr, DecidableEq, Inhabited

/-! ## URLs -/

def hexUpper (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- RFC 3986's unreserved characters, which a query component keeps as they are. -/
def unreserved (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) ||
    b == 45 || b == 46 || b == 95 || b == 126

/-- Percent-encode a query component (UTF-8; everything but the unreserved characters). -/
def percentEncode (s : String) : String :=
  String.ofList (s.toUTF8.toList.flatMap fun b =>
    if unreserved b then [Char.ofNat b.toNat]
    else ['%', hexUpper (b.toNat / 16), hexUpper (b.toNat % 16)])

/-- `k=v&k=v`, each part percent-encoded. -/
def queryString (params : List (String × String)) : String :=
  "&".intercalate (params.map fun (k, v) => percentEncode k ++ "=" ++ percentEncode v)

/-- A service URL without its trailing slashes: `https://bsky.social/` is `https://bsky.social`. -/
def trimService (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (· == '/')).reverse)

/-- `<service>/xrpc/<nsid>`, then `?<params>` when there are any. -/
def xrpcUrl (service nsid : String) (params : List (String × String)) : String :=
  trimService service ++ "/xrpc/" ++ nsid ++
    (if params.isEmpty then "" else "?" ++ queryString params)

/-- A query: GET, parameters in the URL. -/
def query (service nsid : String) (params : List (String × String) := [])
    (secret : Option KeychainSecret := none) : Http :=
  { method := .get, url := xrpcUrl service nsid params,
    headers := [("Accept", "application/json")], secret }

/-- A procedure: POST with a JSON body. -/
def procedure (service nsid : String) (body : Json) (secret : Option KeychainSecret := none)
    (capture : List (String × String) := []) (redact : Bool := false) : Http :=
  { method := .post, url := xrpcUrl service nsid [],
    headers := [("Accept", "application/json"), ("Content-Type", "application/json")],
    body := encode body, secret, capture, redact }

/-! ## Errors -/

/-- The error names M4 acts on, and the rest. -/
inductive ErrorName where
  /-- The access token has expired: refresh, then retry. -/
  | expiredToken
  /-- The token is not valid (revoked, or for another service). -/
  | invalidToken
  /-- The request needs a session and had none. -/
  | authRequired
  | rateLimitExceeded
  /-- Any other name (`InvalidRequest`, `AccountTakedown`, …), as written. -/
  | other (name : String)
deriving Repr, DecidableEq, Inhabited

def ErrorName.ofString : String → ErrorName
  | "ExpiredToken" => .expiredToken
  | "InvalidToken" => .invalidToken
  | "AuthRequired" => .authRequired
  | "RateLimitExceeded" => .rateLimitExceeded
  | s => .other s

def ErrorName.toString : ErrorName → String
  | .expiredToken => "ExpiredToken"
  | .invalidToken => "InvalidToken"
  | .authRequired => "AuthRequired"
  | .rateLimitExceeded => "RateLimitExceeded"
  | .other s => s

/-- An XRPC error body. A body that isn't one (HTML from a proxy, nothing at all) is
`other ""` with no message. -/
structure XrpcError where
  name : ErrorName
  message : Option String := none
deriving Repr, DecidableEq, Inhabited

def XrpcError.ofJson (j : Json) : XrpcError :=
  { name := ErrorName.ofString ((j.str? "error").getD ""), message := j.str? "message" }

def XrpcError.toJson (e : XrpcError) : Json :=
  .obj ([("error", .str e.name.toString)] ++ opt "message" Json.str e.message)

/-- The error in a reply body, whatever it holds. -/
def XrpcError.ofBody (body : ByteArray) : XrpcError :=
  match decodeBytes body with
  | some j => XrpcError.ofJson j
  | none => { name := .other "" }

/-- Whether a header name matches, ignoring ASCII case. -/
def headerIs (want : String) (name : String) : Bool := name.toLower == want.toLower

/-- The `ratelimit-reset` header: when the limit resets, in seconds since the epoch. -/
def ratelimitReset (headers : List (String × String)) : Option Nat :=
  (headers.find? (headerIs "ratelimit-reset" ·.1)).bind (·.2.trimAscii.toString.toNat?)

/-! ## Replies -/

/-- What a call came to. -/
inductive Outcome (α : Type) where
  /-- A 2xx reply whose body decoded. -/
  | ok (v : α)
  /-- A non-2xx reply: its status, the error in its body and `ratelimit-reset`. -/
  | error (status : Nat) (e : XrpcError) (reset : Option Nat)
  /-- A 2xx reply whose body isn't what the lexicon says. -/
  | malformed (status : Nat)
  /-- The request never got a response (the host's fault and message). -/
  | failed (fault : Cairn.Fault) (message : String)
  /-- The session didn't send it: signed out, or its refresh was refused. -/
  | notSent
deriving Repr, Inhabited

def isSuccess (status : Nat) : Bool := 200 ≤ status && status < 300

/-- A reply read with a decoder. -/
def Outcome.ofReply {α : Type} (decode : Json → Option α) : Cairn.Reply → Outcome α
  | .http status headers body =>
    if isSuccess status then
      match (decodeBytes body).bind decode with
      | some v => .ok v
      | none => .malformed status
    else .error status (XrpcError.ofBody body) (ratelimitReset headers)
  | .failed f m => .failed f m
  | _ => .failed .invalid "not an http reply"

/-- The error name of a non-2xx http reply. -/
def errorOf : Cairn.Reply → Option ErrorName
  | .http status _ body => if isSuccess status then none else some (XrpcError.ofBody body).name
  | _ => none

end CairnAtproto
