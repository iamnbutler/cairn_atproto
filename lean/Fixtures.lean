import CairnAtproto

/-! `lake exe fixtures FILE…`: decodes each recorded or synthesized response
(`fixtures/`) with the decoder its name says, and prints what it read, one line per fact:

* `ok <file> <kind> <n>`, or `FAIL <file>` (the exit status is then 1);
* for a feed page, `embed <kind>` and `reason <kind>` per item and `reply <kind>` per parent;
* `date <text> <ms>` for every `createdAt` and `indexedAt` it read (`-` if it didn't parse),
  which `tools/check-fixtures.py` compares with Python's `datetime`;
* `encode <file> ok` when `ofJson (toJson v)` gives `v` back on the decoded value. -/

open CairnJson CairnAtproto

def embedKind : Embed → String
  | .images is => s!"images:{is.length}"
  | .external _ => "external"
  | .record q => s!"record:{quoteKind q}"
  | .recordWithMedia q m => s!"recordWithMedia:{quoteKind q}:{mediaKind m}"
  | .other t => s!"other:{t}"
where
  quoteKind : Quote → String
    | .post _ => "post" | .notFound _ => "notFound" | .blocked _ => "blocked"
    | .detached _ => "detached" | .other t => s!"other({t})"
  mediaKind : Media → String
    | .images is => s!"images:{is.length}" | .external _ => "external" | .other t => s!"other({t})"

def refKind : ReplyRef → String
  | .post _ => "post" | .notFound _ => "notFound" | .blocked _ => "blocked" | .other t => s!"other:{t}"

def date (s : String) : String :=
  s!"date {s} {match parseDatetime s with | some ms => toString ms | none => "-"}"

def postDates (p : Post) : List String :=
  [date p.createdAt, date p.indexedAt]

def feedLines (pg : FeedPage) : List String :=
  pg.feed.flatMap fun i =>
    [s!"embed {(i.post.embed.map embedKind).getD "none"}",
     s!"reason {match i.reason with | some (.repost _ _) => "repost" | some (.other t) => s!"other:{t}" | none => "none"}"]
    ++ (match i.reply with | some r => [s!"reply {refKind r.parent}"] | none => [])
    ++ postDates i.post
    ++ (match i.post.embed with
        | some (.record (.post q)) | some (.recordWithMedia (.post q) _) => [date q.createdAt]
        | _ => [])

def check (path : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile path
  let name := (System.FilePath.mk path).fileName.getD path
  let some j := decodeBytes bytes | IO.println s!"FAIL {path} (not JSON)"; return false
  if name.startsWith "error" then
    let e := XrpcError.ofJson j
    IO.println s!"ok {path} error {e.name.toString}"
    return true
  if name.startsWith "session" then
    match SessionInfo.ofJson j with
    | some s =>
      IO.println s!"ok {path} session {s.handle} pds={s.pds.getD "-"}"
      if SessionInfo.ofJson s.toJson == some s then IO.println s!"encode {path} ok"
      else IO.println s!"FAIL {path} encode"; return false
      return true
    | none => IO.println s!"FAIL {path}"; return false
  match FeedPage.ofJson j with
  | some pg =>
    IO.println s!"ok {path} feed {pg.feed.length}"
    for l in feedLines pg do IO.println l
    if FeedPage.ofJson pg.toJson == some pg then IO.println s!"encode {path} ok"
    else IO.println s!"FAIL {path} encode"; return false
    return true
  | none => IO.println s!"FAIL {path}"; return false

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  for a in args do
    ok := (← check a) && ok
  return if ok then 0 else 1
