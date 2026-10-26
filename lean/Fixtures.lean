import CairnAtproto

/-! `lake exe fixtures FILE…`: decodes each recorded or synthesized response
(`fixtures/`) with the decoder its name says, and prints what it read, one line per fact:

* `ok <file> <kind> <n>`, or `FAIL <file>` (the exit status is then 1);
* for a feed page, `embed <kind>` and `reason <kind>` per item and `reply <kind>` per parent;
* `date <text> <ms>` for every `createdAt` and `indexedAt` it read (`-` if it didn't parse),
  which `tools/check-fixtures.py` compares with Python's `datetime`;
* `viewer …` for a post's or profile's viewer state when it isn't the default;
* for notifications, `notification <reason> <read|unread> text=<y|n> subject=<y|n>` per item;
* `encode <file> ok` when `ofJson (toJson v)` gives `v` back on the decoded value.

The decoder by name: `error*` `XrpcError`, `session*` `SessionInfo`, `getProfile*`
`ProfileDetail`, `getPosts*` `Posts`, `listNotifications*` `NotificationPage`,
`getUnreadCount*` `unreadCountOf`, `getRecord*` `RecordView`, `putRecord*`
`StrongRef.ofPutReply`, anything else `FeedPage`. -/

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

def profileViewerLines (who : String) (v : ProfileViewer) : List String :=
  if v = {} then [] else
    [s!"viewer {who} muted={v.muted} blockedBy={v.blockedBy} blocking={v.blocking.isSome} following={v.following.isSome} followedBy={v.followedBy.isSome}"]

def postViewerLines (p : Post) : List String :=
  (if p.viewer = {} then [] else
    [s!"viewer post like={p.viewer.like.isSome} repost={p.viewer.repost.isSome}"])
  ++ profileViewerLines "author" p.author.viewer
  ++ (if p.reply.isSome then ["record reply"] else [])

def recordKind : CairnAtproto.Record → String
  | .like .. => "like" | .repost .. => "repost" | .follow .. => "follow" | .other t => s!"other:{t}"

def feedLines (pg : FeedPage) : List String :=
  pg.feed.flatMap fun i =>
    postViewerLines i.post ++ [s!"embed {(i.post.embed.map embedKind).getD "none"}",
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
  let enc (ok : Bool) : IO Bool := do
    if ok then IO.println s!"encode {path} ok"; return true
    else IO.println s!"FAIL {path} encode"; return false
  if name.startsWith "getProfile" then
    match ProfileDetail.ofJson j with
    | some d =>
      IO.println s!"ok {path} profile {d.profile.handle} posts={d.postsCount}"
      for l in profileViewerLines "profile" d.profile.viewer do IO.println l
      return ← enc (ProfileDetail.ofJson d.toJson == some d)
    | none => IO.println s!"FAIL {path}"; return false
  if name.startsWith "getPosts" then
    match Posts.ofJson j with
    | some ps =>
      IO.println s!"ok {path} posts {ps.posts.length}"
      for p in ps.posts do
        for l in postViewerLines p ++ postDates p do IO.println l
      return ← enc (Posts.ofJson ps.toJson == some ps)
    | none => IO.println s!"FAIL {path}"; return false
  if name.startsWith "listNotifications" then
    match NotificationPage.ofJson j with
    | some pg =>
      IO.println s!"ok {path} notifications {pg.notifications.length} cursor={pg.cursor.isSome} seenAt={pg.seenAt.isSome}"
      for n in pg.notifications do
        IO.println s!"notification {n.reason.toString} {if n.isRead then "read" else "unread"} text={if n.text.isSome then "y" else "n"} subject={if n.reasonSubject.isSome then "y" else "n"}"
        for l in profileViewerLines "author" n.author.viewer do IO.println l
        IO.println (date n.indexedAt)
      return ← enc (NotificationPage.ofJson pg.toJson == some pg)
    | none => IO.println s!"FAIL {path}"; return false
  if name.startsWith "getUnreadCount" then
    match unreadCountOf j with
    | some n => IO.println s!"ok {path} unread {n}"; return true
    | none => IO.println s!"FAIL {path}"; return false
  if name.startsWith "getRecord" then
    match RecordView.ofJson j with
    | some r =>
      IO.println s!"ok {path} record {recordKind r.value} uri={(AtUri.parse r.uri).isSome}"
      return ← enc (RecordView.ofJson r.toJson == some r)
    | none => IO.println s!"FAIL {path}"; return false
  if name.startsWith "putRecord" then
    match StrongRef.ofPutReply j with
    | some r => IO.println s!"ok {path} written uri={(AtUri.parse r.uri).isSome}"; return true
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
