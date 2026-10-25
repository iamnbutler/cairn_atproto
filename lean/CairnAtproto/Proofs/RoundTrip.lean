module

public import CairnAtproto.Lexicon.Feed
public import CairnAtproto.Lexicon.Server

/-! # Round trips

`ofJson (toJson v) = some v` for every lexicon type with an encoder, at the `Json` level, and
with `CairnJson.decode_encode` at the text level for the types a fake server sends whole
(`FeedPage`, `SessionInfo`, `XrpcError`). -/

@[expose] public section

namespace CairnAtproto
open CairnJson

theorem optMap_map {α β : Type} (f : β → Option α) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f (g x) = some x) → optMap f (xs.map g) = some xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, optMap, h x (List.mem_cons_self ..),
      optMap_map f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

@[simp] theorem asObj_obj (kvs : List (String × Json)) : Json.asObj (.obj kvs) = some (.obj kvs) :=
  rfl

theorem Profile.ofJson_toJson (p : Profile) : Profile.ofJson p.toJson = some p := by
  obtain ⟨did, handle, dn, av⟩ := p
  cases dn <;> cases av <;>
    simp [Profile.ofJson, Profile.toJson, opt, Json.str?, Json.field, List.find?, Json.getStr]

theorem Image.ofJson_toJson (i : Image) : Image.ofJson i.toJson = some i := by
  obtain ⟨thumb, full, alt, aspect⟩ := i
  cases aspect <;>
    simp [Image.ofJson, Image.toJson, opt, aspectOf, aspectJson, Json.obj?, Json.nat?, Json.asNat,
      Json.ofNat, Json.str?, Json.field, List.find?, Json.getStr]

theorem External.ofJson_toJson (e : External) : External.ofJson e.toJson = some e := by
  obtain ⟨uri, title, desc, thumb⟩ := e
  cases thumb <;>
    simp [External.ofJson, External.toJson, opt, Json.str?, Json.field, List.find?, Json.getStr]

@[simp] theorem Profile.asObj_toJson (p : Profile) : Json.asObj p.toJson = some p.toJson := rfl

theorem QuotedPost.ofJson_toJson (q : QuotedPost) : QuotedPost.ofJson q.toJson = some q := by
  obtain ⟨uri, cid, author, text, createdAt, indexedAt⟩ := q
  simp [QuotedPost.ofJson, QuotedPost.toJson, Json.obj?, Json.str?, Json.field, List.find?,
    Json.getStr, Profile.ofJson_toJson]

@[simp] theorem QuotedPost.asObj_toJson (q : QuotedPost) : Json.asObj q.toJson = some q.toJson := rfl
@[simp] theorem QuotedPost.type_toJson (q : QuotedPost) : Json.type q.toJson = tViewRecord := by
  simp [QuotedPost.toJson, Json.type, Json.str?, Json.field, List.find?, Json.getStr]

theorem Quote.ofJson_toJson (q : Quote) : Quote.ofJson q.toJson = q := by
  cases q with
  | post p => simp [Quote.ofJson, Quote.toJson, QuotedPost.ofJson_toJson]
  | other t =>
    simp only [Quote.ofJson, Quote.toJson]
    simp [Json.type, Json.str?, Json.field, List.find?, Json.getStr, QuotedPost.ofJson, Json.obj?]
  | _ =>
    simp [Quote.ofJson, Quote.toJson, Json.type, Json.str?, Json.field, List.find?, Json.getStr,
      tViewRecord, tViewNotFound, tViewBlocked, tViewDetached]

@[simp] theorem Quote.asObj_toJson (q : Quote) : Json.asObj q.toJson = some q.toJson := by
  cases q <;> rfl

@[simp] theorem External.asObj_toJson (e : External) : Json.asObj e.toJson = some e.toJson := rfl

theorem imagesOf_imagesJson (is : List Image) : imagesOf (imagesJson is) = some is := by
  simp [imagesOf, imagesJson, Json.arr?, Json.field, List.find?, Json.getArr,
    optMap_map Image.ofJson Image.toJson is (fun i _ => Image.ofJson_toJson i)]

theorem externalOf_externalJson (e : External) : externalOf (externalJson e) = some e := by
  simp [externalOf, externalJson, Json.obj?, Json.field, List.find?, External.ofJson_toJson]

@[simp] theorem type_imagesJson (is : List Image) : Json.type (imagesJson is) = tImagesView := by
  simp [imagesJson, Json.type, Json.str?, Json.field, List.find?, Json.getStr]
@[simp] theorem type_externalJson (e : External) : Json.type (externalJson e) = tExternalView := by
  simp [externalJson, Json.type, Json.str?, Json.field, List.find?, Json.getStr]

/-- A lone `{"$type": t}`: its type, and no other member. -/
theorem type_lone (t : String) : Json.type (.obj [("$type", .str t)]) = t := by
  simp [Json.type, Json.str?, Json.field, List.find?, Json.getStr]

theorem imagesOf_lone (t : String) : imagesOf (.obj [("$type", .str t)]) = none := by
  simp [imagesOf, Json.arr?, Json.field, List.find?]
theorem externalOf_lone (t : String) : externalOf (.obj [("$type", .str t)]) = none := by
  simp [externalOf, Json.obj?, Json.field, List.find?]

theorem Media.ofJson_toJson (m : Media) : Media.ofJson m.toJson = m := by
  cases m with
  | images is => simp [Media.ofJson, Media.toJson, imagesOf_imagesJson]
  | external e =>
    simp [Media.ofJson, Media.toJson, externalOf_externalJson, tImagesView, tExternalView]
  | other t => simp [Media.ofJson, Media.toJson, type_lone, imagesOf_lone, externalOf_lone]

@[simp] theorem Media.asObj_toJson (m : Media) : Json.asObj m.toJson = some m.toJson := by
  cases m <;> rfl

theorem Embed.ofJson_toJson (e : Embed) : Embed.ofJson e.toJson = e := by
  cases e with
  | images is => simp [Embed.ofJson, Embed.toJson, imagesOf_imagesJson]
  | external x =>
    simp [Embed.ofJson, Embed.toJson, externalOf_externalJson, tImagesView, tExternalView]
  | record q =>
    simp [Embed.ofJson, Embed.toJson, Json.type, Json.str?, Json.field, List.find?, Json.getStr,
      Json.obj?, Quote.ofJson_toJson, tImagesView, tExternalView, tRecordView]
  | recordWithMedia q m =>
    simp [Embed.ofJson, Embed.toJson, Json.type, Json.str?, Json.field, List.find?, Json.getStr,
      Json.obj?, Quote.ofJson_toJson, Media.ofJson_toJson, tImagesView, tExternalView, tRecordView,
      tRecordWithMediaView]
  | other t =>
    simp [Embed.ofJson, Embed.toJson, type_lone, imagesOf_lone, externalOf_lone, Json.obj?,
      Json.field, List.find?]

@[simp] theorem Embed.asObj_toJson (e : Embed) : Json.asObj e.toJson = some e.toJson := by
  cases e <;> rfl

theorem Post.ofJson_toJson (p : Post) : Post.ofJson p.toJson = some p := by
  obtain ⟨uri, cid, author, text, createdAt, embed, rc, rp, lc, qc, indexedAt⟩ := p
  cases embed <;>
    simp [Post.ofJson, Post.toJson, opt, recordText, Json.obj?, Json.str?, Json.nat?, Json.asNat,
      Json.ofNat, Json.field, List.find?, Json.getStr, Profile.ofJson_toJson, Embed.ofJson_toJson]

@[simp] theorem Post.asObj_toJson (p : Post) : Json.asObj p.toJson = some p.toJson := rfl

theorem ReplyRef.ofJson_toJson (r : ReplyRef) : ReplyRef.ofJson r.toJson = r := by
  cases r with
  | post p =>
    obtain ⟨uri, cid, author, text, createdAt, embed, rc, rp, lc, qc, indexedAt⟩ := p
    cases embed <;>
      simp [ReplyRef.ofJson, ReplyRef.toJson, Post.toJson, Post.ofJson, opt, recordText,
        Json.type, Json.obj?, Json.str?, Json.nat?, Json.asNat, Json.ofNat, Json.field, List.find?,
        Json.getStr, Profile.ofJson_toJson, Embed.ofJson_toJson, tPostView, tNotFoundPost,
        tBlockedPost]
  | other t =>
    simp [ReplyRef.ofJson, ReplyRef.toJson, type_lone, Post.ofJson, Json.str?, Json.field,
      List.find?]
  | _ =>
    simp [ReplyRef.ofJson, ReplyRef.toJson, Json.type, Json.str?, Json.field, List.find?,
      Json.getStr, tNotFoundPost, tBlockedPost]

@[simp] theorem ReplyRef.asObj_toJson (r : ReplyRef) : Json.asObj r.toJson = some r.toJson := by
  cases r <;> rfl

theorem ReplyCtx.ofJson_toJson (r : ReplyCtx) : ReplyCtx.ofJson r.toJson = some r := by
  obtain ⟨root, parent, gp⟩ := r
  cases gp <;>
    simp [ReplyCtx.ofJson, ReplyCtx.toJson, opt, Json.obj?, Json.field, List.find?,
      ReplyRef.ofJson_toJson, Profile.ofJson_toJson]

theorem Reason.ofJson_toJson (r : Reason) : Reason.ofJson r.toJson = r := by
  cases r with
  | repost p at_ =>
    simp [Reason.ofJson, Reason.toJson, Json.type, Json.obj?, Json.str?, Json.field, List.find?,
      Json.getStr, Profile.ofJson_toJson]
  | other t =>
    simp [Reason.ofJson, Reason.toJson, type_lone, Json.obj?, Json.str?, Json.field, List.find?]

@[simp] theorem Reason.asObj_toJson (r : Reason) : Json.asObj r.toJson = some r.toJson := by
  cases r <;> rfl
@[simp] theorem ReplyCtx.asObj_toJson (r : ReplyCtx) : Json.asObj r.toJson = some r.toJson := rfl

theorem FeedItem.ofJson_toJson (i : FeedItem) : FeedItem.ofJson i.toJson = some i := by
  obtain ⟨post, reply, reason⟩ := i
  cases reply <;> cases reason <;>
    simp [FeedItem.ofJson, FeedItem.toJson, opt, Json.obj?, Json.field, List.find?,
      Post.ofJson_toJson, ReplyCtx.ofJson_toJson, Reason.ofJson_toJson]

theorem FeedPage.ofJson_toJson (p : FeedPage) : FeedPage.ofJson p.toJson = some p := by
  obtain ⟨feed, cursor⟩ := p
  cases cursor <;>
    simp [FeedPage.ofJson, FeedPage.toJson, opt, Json.arr?, Json.str?, Json.field, List.find?,
      Json.getArr, Json.getStr,
      optMap_map FeedItem.ofJson FeedItem.toJson feed (fun i _ => FeedItem.ofJson_toJson i)]

theorem SessionInfo.ofJson_toJson (s : SessionInfo) : SessionInfo.ofJson s.toJson = some s := by
  obtain ⟨did, handle, email, active, pds⟩ := s
  cases email <;> cases active <;> cases pds <;>
    simp [SessionInfo.ofJson, SessionInfo.toJson, opt, didDocJson, didDocPds, pdsOf, isPdsId,
      Json.obj?, Json.str?, Json.bool?, Json.arr?, Json.field, List.find?, Json.getStr,
      Json.getBool, Json.getArr]

/-- An error name reads back as itself when it is written as `ofString` would read it (an
`other` name is none of the four). -/
def ErrorName.Canonical (n : ErrorName) : Prop := ErrorName.ofString n.toString = n

theorem ErrorName.toString_ofString (s : String) : (ErrorName.ofString s).toString = s := by
  unfold ErrorName.ofString
  split <;> rfl

theorem XrpcError.ofJson_toJson (e : XrpcError) (h : e.name.Canonical) :
    XrpcError.ofJson e.toJson = e := by
  obtain ⟨name, message⟩ := e
  cases message <;>
    simp_all [XrpcError.ofJson, XrpcError.toJson, opt, Json.str?, Json.field, List.find?,
      Json.getStr, ErrorName.Canonical]

/-! ## The session decoders never read a token -/

def isTokenKey (k : String) : Bool := k == "accessJwt" || k == "refreshJwt"

/-- Members with each token's value replaced by `v k` (anything at all). -/
def replaceTokens (v : String → Json) (kv : String × Json) : String × Json :=
  if isTokenKey kv.1 then (kv.1, v kv.1) else kv

theorem field_replaceTokens (v : String → Json) (k : String) (hk : isTokenKey k = false) :
    ∀ kvs : List (String × Json),
      Json.field (.obj (kvs.map (replaceTokens v))) k = Json.field (.obj kvs) k
  | [] => rfl
  | (k0, x) :: kvs => by
    have ih := field_replaceTokens v k hk kvs
    simp only [Json.field] at ih ⊢
    by_cases h0 : isTokenKey k0 = true
    · have hne : (k0 == k) = false := by
        cases hkk : (k0 == k)
        · rfl
        · rw [beq_iff_eq] at hkk; subst hkk; rw [h0] at hk; cases hk
      simp only [List.map_cons, List.find?_cons, replaceTokens, h0, ite_true, hne, ih]
    · simp only [List.map_cons, List.find?_cons, replaceTokens, h0, ite_false, Bool.false_eq_true]
      split
      · rfl
      · exact ih

/-- Whatever the tokens' members hold (the blanks the host writes, the real tokens, anything),
`SessionInfo.ofJson` reads the same account: it never reads a token. -/
theorem SessionInfo.ofJson_replaceTokens (v : String → Json) (kvs : List (String × Json)) :
    SessionInfo.ofJson (.obj (kvs.map (replaceTokens v))) = SessionInfo.ofJson (.obj kvs) := by
  simp only [SessionInfo.ofJson, Json.str?, Json.bool?, Json.obj?,
    field_replaceTokens v "did" rfl, field_replaceTokens v "handle" rfl,
    field_replaceTokens v "email" rfl, field_replaceTokens v "active" rfl,
    field_replaceTokens v "didDoc" rfl]

end CairnAtproto
