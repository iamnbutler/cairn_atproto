module

public import CairnAtproto.Xrpc

/-! # `com.atproto.server`: the session calls

`createSession`, `refreshSession` and `getSession` answer the same account fields. Their
`accessJwt` and `refreshJwt` are the host's: cairn#205 captures them into the Keychain items
`access` and `refresh` and blanks them before Lean sees the body, and `SessionInfo` has no
field for them, so no decoder here ever reads one (`SessionInfo.ofJson_blank` in
`CairnAtproto.Proofs.RoundTrip`).

The account's PDS comes from its DID document: the service with id `#atproto_pds` (or
`<did>#atproto_pds`), its `serviceEndpoint`. -/

@[expose] public section

namespace CairnAtproto
open CairnJson

/-- An account as the session calls describe it. No tokens, by construction. -/
structure SessionInfo where
  did : String
  handle : String
  email : Option String := none
  /-- `false` for a deactivated or taken-down account; absent means active. -/
  active : Option Bool := none
  /-- The `#atproto_pds` service endpoint from the DID document, if it has one. -/
  pds : Option String := none
deriving Repr, DecidableEq, Inhabited

/-- Whether a DID-document service id names the account's PDS. -/
def isPdsId (id : String) : Bool := id == "#atproto_pds" || id.endsWith "#atproto_pds"

/-- The PDS endpoint of a DID document's `service` list: the first `#atproto_pds` entry. -/
def pdsOf : List Json → Option String
  | [] => none
  | s :: rest =>
    if isPdsId ((s.str? "id").getD "") then
      match s.str? "serviceEndpoint" with
      | some e => some e
      | none => pdsOf rest
    else pdsOf rest

/-- The PDS endpoint of a DID document. -/
def didDocPds (doc : Json) : Option String := (doc.arr? "service").bind pdsOf

def SessionInfo.ofJson (j : Json) : Option SessionInfo := do
  let did ← j.str? "did"
  let handle ← j.str? "handle"
  some { did, handle, email := j.str? "email", active := j.bool? "active",
         pds := (j.obj? "didDoc").bind didDocPds }

/-- A DID document with just the PDS service, as `SessionInfo.toJson` writes it. -/
def didDocJson (did pds : String) : Json :=
  .obj [("id", .str did), ("service", .arr [.obj [("id", .str "#atproto_pds"),
    ("type", .str "AtprotoPersonalDataServer"), ("serviceEndpoint", .str pds)]])]

/-- The reply body a server would send, with the tokens blank as Lean receives them (the fake
PDS of cairn#208 writes these). -/
def SessionInfo.toJson (s : SessionInfo) : Json :=
  .obj ([("accessJwt", .str ""), ("refreshJwt", .str ""), ("did", .str s.did),
    ("handle", .str s.handle)] ++ opt "email" Json.str s.email ++ opt "active" Json.bool s.active
    ++ opt "didDoc" (didDocJson s.did) s.pds)

/-! ## Requests -/

def nsidCreateSession : String := "com.atproto.server.createSession"
def nsidRefreshSession : String := "com.atproto.server.refreshSession"
def nsidGetSession : String := "com.atproto.server.getSession"

/-- What the session calls capture: both tokens, into the two items. -/
def sessionCapture : List (String × String) :=
  [("accessJwt", accessItem), ("refreshJwt", refreshItem)]

/-- `createSession`: the identifier (handle or email) and the app password, in the one request
that ever carries the password, marked `redact`. -/
def createSession (service identifier password : String) : Http :=
  procedure service nsidCreateSession
    (.obj [("identifier", .str identifier), ("password", .str password)])
    (capture := sessionCapture) (redact := true)

/-- `refreshSession`: authorised by the refresh token, capturing the new pair. A POST with no
body (the procedure takes no input). -/
def refreshSession (service : String) : Http :=
  { method := .post, url := xrpcUrl service nsidRefreshSession [],
    headers := [("Accept", "application/json")], secret := some { account := refreshItem },
    capture := sessionCapture }

/-- `getSession`: authorised by the access token. -/
def getSession (service : String) : Http :=
  query service nsidGetSession (secret := some { account := accessItem })

end CairnAtproto
