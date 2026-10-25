import CairnAtproto.Proofs.RoundTrip
import CairnJsonProofs.RoundTrip


/-! # Depth bounds, and round trips as text

Every encoded lexicon value nests at most a few levels deep, well within `CairnJson.maxDepth`,
so `CairnJson.decode_encode` applies to it. -/

set_option linter.unusedSimpArgs false

namespace CairnAtproto
open CairnJson

theorem depthList_map_le {α : Type} (g : α → Json) (n : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, (g x).depth ≤ n) → Json.depth.depthList (xs.map g) ≤ n
  | [], _ => Nat.zero_le _
  | x :: xs, h => by
    simp only [List.map_cons, Json.depth.depthList]
    exact Nat.max_le.2 ⟨h x (List.mem_cons_self ..),
      depthList_map_le g n xs (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

theorem Profile.depth_toJson (p : Profile) : p.toJson.depth ≤ 1 := by
  obtain ⟨_, _, dn, av⟩ := p
  cases dn <;> cases av <;> simp [Profile.toJson, opt, Json.depth, Json.depth.depthMembers]

theorem Image.depth_toJson (i : Image) : i.toJson.depth ≤ 2 := by
  obtain ⟨_, _, _, a⟩ := i
  cases a <;> simp [Image.toJson, opt, aspectJson, Json.depth, Json.depth.depthMembers, Json.ofNat]

theorem External.depth_toJson (e : External) : e.toJson.depth ≤ 1 := by
  obtain ⟨_, _, _, t⟩ := e
  cases t <;> simp [External.toJson, opt, Json.depth, Json.depth.depthMembers, Json.ofNat]

theorem QuotedPost.depth_toJson (q : QuotedPost) : q.toJson.depth ≤ 2 := by
  have := Profile.depth_toJson q.author
  simp [QuotedPost.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega

theorem Quote.depth_toJson (q : Quote) : q.toJson.depth ≤ 2 := by
  cases q with
  | post p => exact QuotedPost.depth_toJson p
  | _ => simp [Quote.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]

theorem imagesJson_depth (is : List Image) : (imagesJson is).depth ≤ 4 := by
  have := depthList_map_le Image.toJson 2 is (fun i _ => Image.depth_toJson i)
  simp [imagesJson, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega

theorem externalJson_depth (e : External) : (externalJson e).depth ≤ 2 := by
  have := External.depth_toJson e
  simp [externalJson, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega

theorem Media.depth_toJson (m : Media) : m.toJson.depth ≤ 4 := by
  cases m with
  | images is => exact imagesJson_depth is
  | external e => have := externalJson_depth e; simp only [Media.toJson]; omega
  | other t => simp [Media.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]

theorem Embed.depth_toJson (e : Embed) : e.toJson.depth ≤ 5 := by
  cases e with
  | images is => have := imagesJson_depth is; simp only [Embed.toJson]; omega
  | external x => have := externalJson_depth x; simp only [Embed.toJson]; omega
  | record q => have := Quote.depth_toJson q; simp [Embed.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega
  | recordWithMedia q m =>
    have := Quote.depth_toJson q; have := Media.depth_toJson m
    simp [Embed.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega
  | other t => simp [Embed.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]

theorem Post.depth_toJson (p : Post) : p.toJson.depth ≤ 6 := by
  have := Profile.depth_toJson p.author
  cases h : p.embed with
  | none => simp [Post.toJson, h, opt, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega
  | some e => have := Embed.depth_toJson e; simp [Post.toJson, h, opt, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega

theorem ReplyRef.depth_toJson (r : ReplyRef) : r.toJson.depth ≤ 6 := by
  cases r with
  | post p =>
    have := Post.depth_toJson p
    simp only [ReplyRef.toJson, Post.toJson] at this ⊢
    simp only [Json.depth, Json.depth.depthMembers, Json.depth.depthList, Json.ofNat] at this ⊢
    omega
  | _ => simp [ReplyRef.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]

theorem ReplyCtx.depth_toJson (r : ReplyCtx) : r.toJson.depth ≤ 7 := by
  have := ReplyRef.depth_toJson r.root; have := ReplyRef.depth_toJson r.parent
  cases h : r.grandparentAuthor with
  | none => simp [ReplyCtx.toJson, h, opt, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega
  | some g => have := Profile.depth_toJson g; simp [ReplyCtx.toJson, h, opt, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega

theorem Reason.depth_toJson (r : Reason) : r.toJson.depth ≤ 2 := by
  cases r with
  | repost p _ => have := Profile.depth_toJson p; simp [Reason.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]; omega
  | other t => simp [Reason.toJson, Json.depth, Json.depth.depthMembers, Json.ofNat]

theorem FeedItem.depth_toJson (i : FeedItem) : i.toJson.depth ≤ 8 := by
  obtain ⟨post, reply, reason⟩ := i
  have := Post.depth_toJson post
  cases reply with
  | none =>
    cases reason with
    | none => simp [FeedItem.toJson, opt, Json.depth, Json.depth.depthMembers]; omega
    | some y =>
      have := Reason.depth_toJson y
      simp [FeedItem.toJson, opt, Json.depth, Json.depth.depthMembers]; omega
  | some x =>
    have := ReplyCtx.depth_toJson x
    cases reason with
    | none => simp [FeedItem.toJson, opt, Json.depth, Json.depth.depthMembers]; omega
    | some y =>
      have := Reason.depth_toJson y
      simp [FeedItem.toJson, opt, Json.depth, Json.depth.depthMembers]; omega

theorem FeedPage.depth_toJson (p : FeedPage) : p.toJson.depth ≤ 10 := by
  obtain ⟨feed, cursor⟩ := p
  have := depthList_map_le FeedItem.toJson 8 feed (fun i _ => FeedItem.depth_toJson i)
  cases cursor <;> simp [FeedPage.toJson, opt, Json.depth, Json.depth.depthMembers, Json.ofNat] <;> omega

theorem SessionInfo.depth_toJson (s : SessionInfo) : s.toJson.depth ≤ 4 := by
  obtain ⟨_, _, e, a, p⟩ := s
  cases e <;> cases a <;> cases p <;>
    simp [SessionInfo.toJson, opt, didDocJson, Json.depth, Json.depth.depthMembers, Json.depth.depthList]

theorem XrpcError.depth_toJson (e : XrpcError) : e.toJson.depth ≤ 1 := by
  obtain ⟨_, m⟩ := e
  cases m <;> simp [XrpcError.toJson, opt, Json.depth, Json.depth.depthMembers, Json.ofNat]

/-! ## As text

What a server writes (`CairnJson.encode`, either slash style) reads back through
`CairnJson.decode` and the lexicon decoders as the value it encoded. -/

theorem FeedPage.decode_encode (p : FeedPage) (slash : Bool) :
    (decode (encode p.toJson slash)).bind FeedPage.ofJson = some p := by
  rw [CairnJson.decode_encode _ _ (Nat.le_trans (FeedPage.depth_toJson p) (by decide))]
  exact FeedPage.ofJson_toJson p

theorem SessionInfo.decode_encode (s : SessionInfo) (slash : Bool) :
    (decode (encode s.toJson slash)).bind SessionInfo.ofJson = some s := by
  rw [CairnJson.decode_encode _ _ (Nat.le_trans (SessionInfo.depth_toJson s) (by decide))]
  exact SessionInfo.ofJson_toJson s

theorem XrpcError.decode_encode (e : XrpcError) (h : e.name.Canonical) (slash : Bool) :
    (decode (encode e.toJson slash)).map XrpcError.ofJson = some e := by
  rw [CairnJson.decode_encode _ _ (Nat.le_trans (XrpcError.depth_toJson e) (by decide))]
  simp [XrpcError.ofJson_toJson e h]

end CairnAtproto
