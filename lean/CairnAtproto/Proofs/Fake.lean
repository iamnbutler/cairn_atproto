module

public import CairnAtproto.Fake

/-! # The fake PDS: its timeline, its writes, its counts and its notifications

* **The timeline only grows at its head.** Post `k` is `postAt cfg k`, a function of the
  configuration and `k` alone, so the timeline of `length` posts is `timeline cfg length`, and a
  longer one extends it at the head (`timeline_extends`). Every request keeps the configuration
  and never shortens the timeline (`Server.handle_cfg`, `Server.handle_length`,
  `Server.handle_timeline`). A page is a contiguous run of it (`page_feed`, `page_head`), and so is
  a page of the posts the AppView shows when some are left out (`pageWhere_run`: muted accounts).
* **Writes are idempotent, and `getRecord` reads them** (`cairn_atproto^31`): a `putRecord` sent
  twice leaves the server as once (`Server.putRec_twice`), as does a `deleteRecord`
  (`Server.deleteRec_twice`), and one of a record that isn't there changes nothing
  (`Server.deleteRec_missing`); after an acknowledged put the record is what the PDS holds
  (`Server.putRec_reads`), after a delete nothing is (`Server.deleteRec_reads`), and `getRecord`
  answers what it holds (`Server.getRec_found`, `Server.getRec_missing`).
* **A post's like count is the number of like records for it** (`cairn_atproto^32`), the
  tester's included, plus the seeded count of accounts outside the fake; `viewer.like` is set
  exactly when the tester holds one, both from the same run of the log (`viewPost_likeCount`,
  `viewPost_like`, and the same for reposts).
* **Notifications are a contiguous, newest-first run** (`cairn_atproto^33`): a page is a run of
  the list newest first (`runPage_run`, `runPage_head`), as the timeline's is. -/

@[expose] public section

namespace CairnAtproto.Fake

theorem timeline_extends (c : Config) (n m : Nat) :
    timeline c (n + m) = (List.range' n m).reverse.map (postAt c) ++ timeline c n := by
  simp only [timeline, List.range_eq_range']
  rw [show n + m = n + m from rfl, ← List.range'_append_1, List.reverse_append, List.map_append]
  simp

/-- A page is a contiguous run of the timeline: the `n` posts after the newest `L - k`. -/
theorem page_feed (c : Config) (L n k : Nat) (hk : k ≤ L) :
    (page c L n (some k)).feed = ((timeline c L).drop (L - k)).take n := by
  apply List.ext_getElem
  · simp [page, timeline]; omega
  · intro i h1 h2
    simp [page, timeline] at *
    simp [timeline] at h2; congr 1; omega

/-- The head page is the newest `n` posts. -/
theorem page_head (c : Config) (L n : Nat) : (page c L n none).feed = (timeline c L).take n := by
  have := page_feed c L n L (Nat.le_refl L)
  simp only [Nat.sub_self, List.drop_zero] at this
  rw [← this]; rfl

/-- The posts `keep` keeps below `k` are those below `L`, less the newer ones: so a page from a
cursor is a contiguous run of the posts kept. -/
theorem keptBelow_drop (keep : Nat → Bool) (k L : Nat) (hk : k ≤ L) :
    keptBelow keep k =
      (keptBelow keep L).drop (((List.range' k (L - k)).reverse.filter keep).length) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [keptBelow, Nat.add_sub_cancel_left, List.range_eq_range']
  rw [← List.range'_append_1, List.reverse_append, List.filter_append]
  simp only [Nat.zero_add, List.drop_left]

/-- A page of the posts the timeline shows, from a cursor at post `k`, is a contiguous run of
them: the `n` after the newer ones. -/
theorem pageWhere_run (c : Config) (keep : Nat → Bool) (L n k : Nat) (hk : k ≤ L) :
    (pageWhere c keep L n (some k)).1 =
      ((keptBelow keep L).drop (((List.range' k (L - k)).reverse.filter keep).length)).take n := by
  simp only [pageWhere, Option.getD_some]
  rw [keptBelow_drop keep k L hk]

/-- The head page is the newest `n` posts shown. -/
theorem pageWhere_head (c : Config) (keep : Nat → Bool) (L n : Nat) :
    (pageWhere c keep L n none).1 = (keptBelow keep L).take n := rfl

/-! ## Requests keep the configuration and never shorten the timeline -/

/-- What every step of the server keeps: the configuration and the timeline's length. -/
def Same (s s' : Server) : Prop := s'.cfg = s.cfg ∧ s'.length = s.length

theorem Same.refl (s : Server) : Same s s := ⟨rfl, rfl⟩

theorem Same.trans {a b c : Server} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem Server.append_same (s : Server) (ch : Change) (d : Bool) : Same s (s.append ch d) :=
  ⟨rfl, rfl⟩

theorem foldl_same {α : Type} (g : Server → α → Server) (hg : ∀ s a, Same s (g s a)) :
    ∀ (l : List α) (s : Server), Same s (l.foldl g s)
  | [], s => Same.refl s
  | a :: l, s => (hg s a).trans (foldl_same g hg l (g s a))

theorem Server.noticePosts_same (s : Server) (f : Nat) (d : Bool) : Same s (s.noticePosts f d) := by
  unfold Server.noticePosts
  apply foldl_same
  intro s k
  split
  · exact Server.append_same _ _ _
  · exact Same.refl _

theorem Server.act_same (s : Server) (kind : ActKind) (a k : Nat) : Same s (s.act kind a k) := by
  unfold Server.act
  split
  · exact Same.refl _
  · exact Server.append_same _ _ _

theorem Server.othersAct_same (s : Server) (n : Nat) : Same s (s.othersAct n) := by
  unfold Server.othersAct
  split
  · exact Same.refl _
  · split
    · exact Same.refl _
    · exact Server.act_same _ _ _ _

theorem Server.check_ok {s s' : Server} {kind : String} {auth : Option String}
    (h : s.check kind auth = .ok s') : s'.cfg = s.cfg ∧ s'.length = s.length := by
  unfold Server.check at h
  repeat (first | split at h | simp_all)
  all_goals (cases h; simp)

theorem Server.issue_keeps (s : Server) : s.issue.1.cfg = s.cfg ∧ s.issue.1.length = s.length := by
  simp [Server.issue]

theorem Server.createSession_keeps (s : Server) (b : String) : Same s (s.createSession b).1 := by
  unfold Server.createSession
  repeat' split
  all_goals first | exact Same.refl _ | exact Server.issue_keeps s

theorem Server.writeRec_same (s : Server) (col k : String) (r : Record) :
    Same s (s.writeRec col k r).1 := ⟨rfl, rfl⟩

theorem Server.putRec_same (s : Server) (w : PutRecord) : Same s (s.putRec w).1 := by
  unfold Server.putRec
  repeat' split
  all_goals first | exact Same.refl _ | exact Server.writeRec_same _ _ _ _

theorem Server.deleteRec_same (s : Server) (u : AtUri) : Same s (s.deleteRec u).1 := by
  unfold Server.deleteRec
  repeat' split
  all_goals first | exact Same.refl _ | exact Server.append_same _ _ _

theorem Server.setMute_same (s : Server) (m : Bool) (a : String) : Same s (s.setMute m a).1 := by
  unfold Server.setMute
  split
  · exact Same.refl _
  · exact Same.refl _
  · dsimp only
    split
    · exact Same.refl _
    · exact Server.append_same _ _ _

theorem Server.updateSeen_same (s : Server) (b : String) : Same s (s.updateSeen b).1 := by
  unfold Server.updateSeen
  repeat' split
  all_goals first | exact Same.refl _ | exact ⟨rfl, rfl⟩

theorem Server.authed_same (s : Server) (n b : String) (ps : List (String × String)) :
    Same s (s.authed n b ps).1 := by
  unfold Server.authed
  repeat' split
  all_goals first
    | exact Same.refl _
    | exact Server.putRec_same _ _
    | exact Server.deleteRec_same _ _
    | exact Server.setMute_same _ _ _
    | exact Server.updateSeen_same _ _

theorem Server.xrpc_keeps (s : Server) (r : Req) (n : String) (ps : List (String × String)) :
    Same s (s.xrpc r n ps).1 := by
  dsimp only [Server.xrpc]
  repeat' split
  all_goals first
    | exact Same.refl _
    | exact Server.createSession_keeps s r.body
    | (rename_i h; obtain ⟨h1, h2⟩ := Server.check_ok h
       first
         | exact ⟨by simp [Server.issue, h1], by simp [Server.issue, h2]⟩
         | exact (show Same s _ from ⟨h1, h2⟩).trans (Server.authed_same _ _ _ _))

theorem Server.between_cfg (s : Server) : s.between.cfg = s.cfg := by
  unfold Server.between
  rw [(Server.othersAct_same _ _).1, (Server.noticePosts_same _ _ _).1]

theorem Server.between_length (s : Server) : s.length ≤ s.between.length := by
  unfold Server.between
  rw [(Server.othersAct_same _ _).2, (Server.noticePosts_same _ _ _).2]
  simp

theorem Server.control_keeps (s : Server) (c : Control) :
    (s.control c).cfg = s.cfg ∧ s.length ≤ (s.control c).length := by
  cases c with
  | post n =>
    have h := Server.noticePosts_same ({ s with length := s.length + n } : Server) s.length true
    simp only [Server.control, Server.grow]
    exact ⟨h.1, by rw [h.2]; simp⟩
  | act kind actor post =>
    simp only [Server.control]
    repeat' split
    all_goals first
      | exact ⟨(Server.act_same _ _ _ _).1, Nat.le_of_eq (Server.act_same _ _ _ _).2.symm⟩
      | exact ⟨rfl, Nat.le_refl _⟩
  | _ => simp [Server.control]

/-- A request keeps the configuration. -/
theorem Server.handle_cfg (s : Server) (r : Req) : (s.handle r).1.cfg = s.cfg := by
  dsimp only [Server.handle]
  repeat' split
  all_goals first
    | rfl
    | exact Server.between_cfg s
    | exact (Server.xrpc_keeps _ _ _ _).1.trans (Server.between_cfg s)
    | exact (Server.control_keeps _ _).1

/-- A request never shortens the timeline. -/
theorem Server.handle_length (s : Server) (r : Req) : s.length ≤ (s.handle r).1.length := by
  have hb := Server.between_length s
  dsimp only [Server.handle]
  repeat' split
  all_goals first
    | exact Nat.le_refl _
    | exact hb
    | (rw [(Server.xrpc_keeps _ _ _ _).2]; exact hb)
    | exact (Server.control_keeps _ _).2

/-- So the timeline after any run of requests extends the one before at its head. -/
theorem Server.handle_timeline (s : Server) (r : Req) :
    ∃ m, timeline (s.handle r).1.cfg (s.handle r).1.length =
      (List.range' s.length m).reverse.map (postAt s.cfg) ++ timeline s.cfg s.length := by
  refine ⟨(s.handle r).1.length - s.length, ?_⟩
  rw [Server.handle_cfg, ← timeline_extends, Nat.add_sub_cancel' (Server.handle_length s r)]

/-! ## Writes: idempotent, and read back (`cairn_atproto^31`) -/

theorem Facts.find_put (c : Config) (f : Facts) (col k : String) (r : Record) (cid : String) :
    (f.apply c (.put col k r cid)).find col k = some ⟨col, k, r, cid⟩ := by
  simp [Facts.apply, Facts.find]

theorem Facts.find_delete (c : Config) (f : Facts) (col k : String) :
    (f.apply c (.delete col k)).find col k = none := by
  simp only [Facts.apply, Facts.find, Facts.without, List.find?_eq_none, List.mem_filter]
  intro x ⟨_, h⟩ hc
  simp_all

@[simp] theorem Server.append_cfg (s : Server) (ch : Change) (d : Bool) :
    (s.append ch d).cfg = s.cfg := rfl

@[simp] theorem Server.append_now (s : Server) (ch : Change) (d : Bool) :
    (s.append ch d).now = s.now.apply s.cfg ch := rfl

theorem Server.isMe_append (s : Server) (ch : Change) (d : Bool) :
    (s.append ch d).isMe = s.isMe := rfl

/-- A `putRecord` of the record already at its key changes nothing. -/
theorem Server.putRec_noop (s : Server) (w : PutRecord) (old : Rec)
    (h : s.now.find w.record.collection w.rkey = some old) (heq : old.record = w.record) :
    (s.putRec w).1 = s := by
  unfold Server.putRec
  repeat' split
  all_goals simp_all

/-- A `putRecord` changes nothing, or writes the record at its key. -/
theorem Server.putRec_cases (s : Server) (w : PutRecord) :
    (s.putRec w).1 = s ∨ (s.putRec w).1 = (s.writeRec w.record.collection w.rkey w.record).1 := by
  unfold Server.putRec
  repeat' split
  all_goals simp

theorem Server.writeRec_find (s : Server) (col k : String) (r : Record) :
    ∃ x, (s.writeRec col k r).1.now.find col k = some x ∧ x.record = r := by
  simp [Server.writeRec, Facts.find_put]

/-- A `putRecord` sent twice leaves the server as one did: the second finds the record there. -/
theorem Server.putRec_twice (s : Server) (w : PutRecord) :
    ((s.putRec w).1.putRec w).1 = (s.putRec w).1 := by
  rcases Server.putRec_cases s w with h | h
  · rw [h, h]
  · rw [h]
    obtain ⟨x, hx, hr⟩ := Server.writeRec_find s w.record.collection w.rkey w.record
    exact Server.putRec_noop _ w x hx hr

/-- The status of a JSON answer (`0` for an image or no answer). -/
def Response.status : Response → Nat
  | .json st .. => st
  | _ => 0

/-- After a `putRecord` the server acknowledged, the PDS holds the record at its key. -/
theorem Server.putRec_reads (s : Server) (w : PutRecord) (h : (s.putRec w).2.status = 200) :
    ∃ r, (s.putRec w).1.now.find w.record.collection w.rkey = some r ∧ r.record = w.record := by
  revert h
  unfold Server.putRec
  repeat' split
  all_goals first
    | simp [Server.fail, Response.status]; done
    | (intro _; simp_all; done)
    | (intro _; exact Server.writeRec_find _ _ _ _)

/-- A `deleteRecord` of a record that isn't there changes nothing. -/
theorem Server.deleteRec_missing (s : Server) (u : AtUri) (h : s.now.find u.collection u.rkey = none) :
    (s.deleteRec u).1 = s := by
  unfold Server.deleteRec
  split
  · rfl
  · simp [h]

/-- After a `deleteRecord` the server acknowledged, the PDS holds nothing at the key. -/
theorem Server.deleteRec_reads (s : Server) (u : AtUri) (h : (s.deleteRec u).2.status = 200) :
    (s.deleteRec u).1.now.find u.collection u.rkey = none := by
  revert h
  unfold Server.deleteRec
  split
  · simp [Server.fail, Response.status]
  · split
    · intro _; simp [Facts.find_delete]
    · rename_i hn; intro _; exact hn

/-- A `deleteRecord` sent twice leaves the server as one did. -/
theorem Server.deleteRec_twice (s : Server) (u : AtUri) :
    ((s.deleteRec u).1.deleteRec u).1 = (s.deleteRec u).1 := by
  unfold Server.deleteRec
  repeat' split
  all_goals simp_all [Server.isMe_append, Facts.find_delete]

/-- `getRecord` answers the record the PDS holds at the key, at once. -/
theorem Server.getRec_found (s : Server) (u : AtUri) (r : Rec) (h1 : s.isMe u.repo = true)
    (h : s.now.find u.collection u.rkey = some r) :
    s.getRec u = s.ok ({ uri := recUri s.cfg r, cid := some r.cid, value := r.record } : RecordView).toJson := by
  simp [Server.getRec, h1, h]

/-- and `RecordNotFound` when it holds none. -/
theorem Server.getRec_missing (s : Server) (u : AtUri) (h : s.now.find u.collection u.rkey = none) :
    (s.getRec u).status = 400 := by
  unfold Server.getRec
  repeat' split
  all_goals simp_all [Server.fail, Response.status]

/-- What ^31 claims of the fake's writes. -/
def WritesHold : Prop :=
  (∀ (s : Server) (w : PutRecord), ((s.putRec w).1.putRec w).1 = (s.putRec w).1) ∧
  (∀ (s : Server) (u : AtUri), ((s.deleteRec u).1.deleteRec u).1 = (s.deleteRec u).1) ∧
  (∀ (s : Server) (u : AtUri), s.now.find u.collection u.rkey = none → (s.deleteRec u).1 = s) ∧
  (∀ (s : Server) (w : PutRecord), (s.putRec w).2.status = 200 →
    ∃ r, (s.putRec w).1.now.find w.record.collection w.rkey = some r ∧ r.record = w.record) ∧
  (∀ (s : Server) (u : AtUri), (s.deleteRec u).2.status = 200 →
    (s.deleteRec u).1.now.find u.collection u.rkey = none) ∧
  (∀ (s : Server) (u : AtUri) (r : Rec), s.isMe u.repo = true → s.now.find u.collection u.rkey = some r →
    s.getRec u = s.ok ({ uri := recUri s.cfg r, cid := some r.cid, value := r.record } : RecordView).toJson) ∧
  (∀ (s : Server) (u : AtUri), s.now.find u.collection u.rkey = none → (s.getRec u).status = 400)

theorem writesHold : WritesHold :=
  ⟨Server.putRec_twice, Server.deleteRec_twice, Server.deleteRec_missing, Server.putRec_reads,
   Server.deleteRec_reads, Server.getRec_found, Server.getRec_missing⟩

/-! ## Counts and viewer state (`cairn_atproto^32`) -/

/-- A post's like count is its seeded count plus the like records for it, the tester's
included. -/
theorem viewPost_likeCount (c : Config) (f : Facts) (p : Post) :
    (viewPost c f p).likeCount =
      p.likeCount + (f.likes.filter (·.2 == p.uri)).length + (f.myLikes p.uri).length := by
  simp [viewPost, Facts.likeCount, Nat.add_assoc]

theorem viewPost_repostCount (c : Config) (f : Facts) (p : Post) :
    (viewPost c f p).repostCount =
      p.repostCount + (f.reposts.filter (·.2 == p.uri)).length + (f.myReposts p.uri).length := by
  simp [viewPost, Facts.repostCount, Nat.add_assoc]

/-- `viewer.like` is set exactly when the same facts hold a like of it by the tester. -/
theorem viewPost_like (c : Config) (f : Facts) (p : Post) :
    (viewPost c f p).viewer.like.isSome = !(f.myLikes p.uri).isEmpty := by
  simp only [viewPost]
  cases f.myLikes p.uri <;> simp

theorem viewPost_repost (c : Config) (f : Facts) (p : Post) :
    (viewPost c f p).viewer.repost.isSome = !(f.myReposts p.uri).isEmpty := by
  simp only [viewPost]
  cases f.myReposts p.uri <;> simp

/-- What ^32 claims of every view. -/
def CountsHold : Prop :=
  ∀ (c : Config) (f : Facts) (p : Post),
    (viewPost c f p).likeCount =
      p.likeCount + (f.likes.filter (·.2 == p.uri)).length + (f.myLikes p.uri).length ∧
    (viewPost c f p).repostCount =
      p.repostCount + (f.reposts.filter (·.2 == p.uri)).length + (f.myReposts p.uri).length ∧
    (viewPost c f p).viewer.like.isSome = !(f.myLikes p.uri).isEmpty ∧
    (viewPost c f p).viewer.repost.isSome = !(f.myReposts p.uri).isEmpty

theorem countsHold : CountsHold := fun c f p =>
  ⟨viewPost_likeCount c f p, viewPost_repostCount c f p, viewPost_like c f p, viewPost_repost c f p⟩

/-! ## Notifications (`cairn_atproto^33`) -/

/-- A page from a cursor at position `k` is a contiguous run of the list, newest first: the `n`
after the `length - k` newest. -/
theorem runPage_run {α : Type} (xs : List α) (n k : Nat) (hk : k ≤ xs.length) :
    (runPage xs n (some k)).1 = (xs.reverse.drop (xs.length - k)).take n := by
  apply List.ext_getElem
  · simp [runPage]; omega
  · intro i h1 h2
    simp only [runPage, Option.getD_some, List.getElem_reverse, List.getElem_drop,
      List.getElem_take, List.length_drop, List.length_take] at *
    congr 1
    simp at h1 h2
    omega

/-- The head page is the newest `n`. -/
theorem runPage_head {α : Type} (xs : List α) (n : Nat) :
    (runPage xs n none).1 = xs.reverse.take n := by
  have := runPage_run xs n xs.length (Nat.le_refl _)
  simp only [Nat.sub_self, List.drop_zero] at this
  rw [← this]; rfl

/-- What ^33 claims of every list of notifications. -/
def NoticesRun : Prop :=
  ∀ (xs : List Notification) (n k : Nat), k ≤ xs.length →
    (runPage xs n (some k)).1 = (xs.reverse.drop (xs.length - k)).take n ∧
    (runPage xs n none).1 = xs.reverse.take n

theorem noticesRun : NoticesRun := fun xs n k hk => ⟨runPage_run xs n k hk, runPage_head xs n⟩

end CairnAtproto.Fake
