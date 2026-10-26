import CairnAtproto

/-! `lake exe fake-pds-model`: the Lean fake PDS (`CairnAtproto.Fake.Server`) over JSON lines,
for `tools/fake-pds/replay.ts`, which sends the same requests to it and to the Bun server and
compares the answers.

The first line is the configuration, `{"seed", "service", "base", "arrival", "life", "act", "lag"}`. Every
later line is a request, `{"method", "path", "authorization"?, "body"?}`, answered by one line:
`{"status", "headers", "body", "delayMs"}` (the body as JSON), `{"png": [w, h]}` or
`{"hang": true}`. It reads until end of input. -/

open CairnJson CairnAtproto CairnAtproto.Fake

def num (j : Json) (k : String) (d : Nat) : Nat := (j.nat? k).getD d

def configOf (j : Json) : Config :=
  { seed := num j "seed" 0, service := (j.str? "service").getD "http://127.0.0.1:2583",
    base := num j "base" 40, arrival := num j "arrival" 3, life := num j "life" 6,
    act := num j "act" 4, lag := num j "lag" 2 }

def answer : Response → Json
  | .json st hs body d => .obj [("status", Json.ofNat st),
      ("headers", .obj (hs.map fun (k, v) => (k, .str v))), ("body", body), ("delayMs", Json.ofNat d)]
  | .png w h => .obj [("png", .arr [Json.ofNat w, Json.ofNat h])]
  | .hang => .obj [("hang", .bool true)]

def reqOf (j : Json) : Req :=
  { method := (j.str? "method").getD "GET", path := (j.str? "path").getD "/",
    authorization := j.str? "authorization", body := (j.str? "body").getD "" }

/-- At most `fuel` requests, one a line. -/
def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : Nat → Server → IO Unit
  | 0, _ => pure ()
  | fuel + 1, s => do
    let line ← stdin.getLine
    if line.isEmpty then return
    match decode line.trimAscii.toString with
    | none =>
      stdout.putStrLn (encode (.obj [("error", .str "not JSON")]))
      stdout.flush
      loop stdin stdout fuel s
    | some j =>
      let (s, r) := s.handle (reqOf j)
      stdout.putStrLn (encode (answer r))
      stdout.flush
      loop stdin stdout fuel s

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let first ← stdin.getLine
  let some cfg := decode first.trimAscii.toString | IO.eprintln "fake-pds-model: the first line is the configuration (JSON)"; return 2
  loop stdin stdout 10000000 (Server.init (configOf cfg))
  return 0
