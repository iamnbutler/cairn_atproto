module

public import CairnAtproto.Paged

/-! # `Paged`'s proofs

Moved from Sky's `Feed` (cairn#250), over any item type and key. A server list `T` is newest
first with keys distinct (`(keys T).Nodup`) and only grows at its head. -/

@[expose] public section

namespace CairnAtproto
namespace Paged

variable {α κ : Type} [Keyed α κ] [DecidableEq κ]

/-! ## A stale page -/

/-- **A load-more page for a cursor the list no longer holds changes nothing it shows**; nor
does an answer to any call but the load-more in flight. -/
theorem gotLoadMore_stale (f : Paged α) (id : Nat) (page : Option (Page α))
    (h : ∀ c, f.loadMore = some (id, c) → f.cursor ≠ some c) :
    (f.gotLoadMore id page).content = f.content := by
  unfold gotLoadMore
  split
  · next l c e =>
    split
    · next hl =>
      subst hl
      have hc := h c e
      split
      · simp only [hc, ↓reduceIte]; rfl
      · rfl
    · rfl
  · rfl

/-! ## A refresh racing a load-more -/

theorem newOnTop_append (a : α) (as p page : List α) :
    newOnTop ((a :: as) ++ p) page = newOnTop (a :: as) page := rfl

/-- **A refresh and a load-more both in flight end the same whichever is answered first**: the
load-more's page (or failure) then the refresh's, or the other way round. -/
theorem race (f : Paged α) (l r : Nat) (c : String) (pl pr : Option (Page α))
    (hl : f.loadMore = some (l, c)) (hc : f.cursor = some c) (hne : f.items ≠ [])
    (hr : f.refresh = some r) :
    (f.gotLoadMore l pl).gotRefresh r pr = (f.gotRefresh r pr).gotLoadMore l pl := by
  obtain ⟨items, cursor, atEnd, lm, rf⟩ := f
  simp only at hl hc hr
  subst hl hc hr
  obtain _ | ⟨a, as⟩ := items
  · exact absurd rfl hne
  cases pl with
  | none =>
    cases pr with
    | none => simp [gotLoadMore, gotRefresh]
    | some q =>
      simp only [gotLoadMore, gotRefresh, headPage, replaceBy, ↓reduceIte]
      split <;> simp
  | some p =>
    cases pr with
    | none => simp [gotLoadMore, gotRefresh, appendPage]
    | some q =>
      simp only [gotLoadMore, gotRefresh, headPage, replaceBy, appendPage, ↓reduceIte]
      rw [newOnTop_append]
      split <;> simp

/-! ## The cursor is never lost -/

/-- A list with items that isn't at its end holds a cursor (where its next page starts). -/
def CursorKept (f : Paged α) : Prop := f.atEnd = false → f.items ≠ [] → f.cursor.isSome = true

instance (f : Paged α) : Decidable (CursorKept f) := by unfold CursorKept; infer_instance

theorem cursorKept_empty : CursorKept ({} : Paged α) := fun _ h => absurd rfl h

theorem cursorKept_append (f : Paged α) (p : Page α) : CursorKept (f.appendPage p) := by
  intro h _
  simp only [appendPage] at h ⊢
  cases hc : p.cursor <;> simp_all

theorem cursorKept_replace (f : Paged α) (p : Page α) : CursorKept (f.replaceBy p) := by
  intro h _
  simp only [replaceBy] at h ⊢
  cases hc : p.cursor <;> simp_all

theorem cursorKept_headPage {f : Paged α} (h : CursorKept f) (p : Page α) :
    CursorKept (f.headPage p) := by
  unfold headPage
  split
  · next new hn =>
    intro ha _
    have hne : f.items ≠ [] := by
      intro e; simp [e, newOnTop] at hn
    exact h ha hne
  · exact cursorKept_replace f p

theorem cursorKept_gotLoadMore {f : Paged α} (h : CursorKept f) (id : Nat) (p : Option (Page α)) :
    CursorKept (f.gotLoadMore id p) := by
  unfold gotLoadMore
  split
  · split
    · split
      · split
        · exact cursorKept_append _ _
        · exact h
      · exact h
    · exact h
  · exact h

theorem cursorKept_gotRefresh {f : Paged α} (h : CursorKept f) (id : Nat) (p : Option (Page α)) :
    CursorKept (f.gotRefresh id p) := by
  unfold gotRefresh
  split
  · split
    · exact cursorKept_headPage (f := { f with refresh := none }) h _
    · exact h
  · exact h

theorem cursorKept_beginLoadMore {f : Paged α} (h : CursorKept f) (id : Nat) :
    ∀ g c, f.beginLoadMore id = some (g, c) → CursorKept g := by
  intro g c e
  unfold beginLoadMore at e
  split at e
  · cases e; exact h
  · cases e

theorem cursorKept_beginRefresh {f : Paged α} (h : CursorKept f) (id : Nat) :
    ∀ g w, f.beginRefresh id = some (g, w) → CursorKept g := by
  intro g w e
  unfold beginRefresh at e
  split at e
  · cases e; exact h
  · cases e

/-- A load-more starts from the cursor the list holds. -/
theorem beginLoadMore_cursor {f : Paged α} {id : Nat} {g : Paged α} {c : String}
    (e : f.beginLoadMore id = some (g, c)) :
    g.loadMore = some (id, c) ∧ g.cursor = some c ∧ g.items = f.items := by
  unfold beginLoadMore at e
  split at e
  · next hc => cases e; exact ⟨rfl, hc, rfl⟩
  · cases e

/-! ## Runs of the server's list -/

/-- `F` is the run of `T` (the server's list, newest first) that starts at position `i`. -/
def IsRun (T : List α) (i : Nat) (F : List α) : Prop :=
  (T.drop i).take F.length = F

theorem run_nil (T : List α) (i : Nat) : IsRun T i [] := by
  simp [IsRun]

/-- A head page is a run. -/
theorem run_head (T : List α) (k : Nat) : IsRun T 0 (T.take k) := by
  simp only [IsRun, List.drop_zero, List.length_take]
  grind

/-- New items at the server's head leave a run a run, further down. -/
theorem run_grow {T : List α} {i : Nat} {F : List α} (N : List α)
    (h : IsRun T i F) : IsRun (N ++ T) (N.length + i) F := by
  simp only [IsRun] at *
  have e : List.drop (N.length + i) N = [] := List.drop_eq_nil_of_le (by omega)
  simpa [List.drop_append, e] using h

/-- A run followed by the run after it is a run. -/
theorem run_append {T : List α} {i : Nat} {F P : List α} (hF : IsRun T i F)
    (hP : IsRun T (i + F.length) P) : IsRun T i (F ++ P) := by
  simp only [IsRun, List.length_append] at *
  rw [List.take_add, hF, List.drop_drop, hP]

theorem run_sublist {T : List α} {i : Nat} {F : List α} (h : IsRun T i F) : F.Sublist T := by
  rw [← h]
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

omit [DecidableEq κ] in
/-- A run of a list without duplicate keys has none. -/
theorem run_nodup {T : List α} {i : Nat} {F : List α} (hT : (keys T).Nodup)
    (h : IsRun T i F) : (keys F).Nodup :=
  hT.sublist ((run_sublist h).map _)

theorem indexOf_spec {k : κ} : ∀ {l : List α} {j : Nat}, indexOf k l = some j →
    ∃ hj : j < l.length, Keyed.key l[j] = k
  | [], _, h => by simp [indexOf] at h
  | x :: xs, j, h => by
    simp only [indexOf] at h
    split at h
    · next e =>
      cases h
      exact ⟨by simp, e⟩
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hlt, e⟩ := indexOf_spec hj'
      exact ⟨by simp; omega, by simpa using e⟩

theorem run_getElem {T : List α} {i : Nat} {a : α} {as : List α}
    (h : IsRun T i (a :: as)) : ∃ hi : i < T.length, T[i] = a := by
  simp only [IsRun] at h
  have hl : 0 < ((T.drop i).take (a :: as).length).length := by rw [h]; simp
  simp only [List.length_take, List.length_drop, List.length_cons] at hl
  refine ⟨by omega, ?_⟩
  have e := congrArg (·[0]?) h
  simp only [List.getElem?_take, List.getElem?_drop, List.length_cons] at e
  simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.add_zero, List.getElem?_cons_zero] at e
  rw [List.getElem?_eq_getElem (by omega)] at e
  exact Option.some.inj e

/-- **A head page holding the list's first item puts exactly the items above it on top**: the
result is the server's list from its head to the list's end. -/
theorem newOnTop_run {T : List α} {i k : Nat} {F new : List α}
    (hT : (keys T).Nodup) (hF : IsRun T i F) (h : newOnTop F (T.take k) = some new) :
    new ++ F = T.take (i + F.length) := by
  obtain _ | ⟨a, as⟩ := F
  · simp [newOnTop] at h
  simp only [newOnTop] at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hjl, ej⟩ := indexOf_spec hj
  obtain ⟨hil, ei⟩ := run_getElem hF
  simp only [List.length_take] at hjl
  have hjT : j < T.length := by omega
  simp only [List.getElem_take] at ej
  have hji : j = i := by
    have hk : (keys T)[j]'(by simp [keys]; omega) = (keys T)[i]'(by simp [keys]; omega) := by
      simp only [keys, List.getElem_map, ej, ei]
    exact (List.Nodup.getElem_inj hT).mp hk
  subst hji
  rw [List.take_take, Nat.min_eq_left (by omega), List.take_add]
  congr 1
  exact hF.symm

/-- **A head page leaves the list a run of the server's**, from the head: the new items on top
of the old run, or the page itself. -/
theorem headPage_run {T : List α} {i k : Nat} (hT : (keys T).Nodup) (f : Paged α)
    (hF : IsRun T i f.items) (cursor : Option String) :
    IsRun T 0 (f.headPage { items := T.take k, cursor }).items := by
  unfold headPage
  split
  · next new h =>
    show IsRun T 0 (new ++ f.items)
    rw [newOnTop_run hT hF h]
    exact run_head T _
  · exact run_head T k

/-- What ^26 claims of the merges, for every server list without duplicate keys: a list that is
a run of it stays a run when the page after it is appended or a head page arrives, also after
new items arrive at the head, and a run has no duplicates. -/
def Contiguous (α : Type) {κ : Type} [Keyed α κ] [DecidableEq κ] : Prop :=
  ∀ T : List α, (keys T).Nodup → ∀ (f : Paged α) (i : Nat), IsRun T i f.items →
    (keys f.items).Nodup ∧
    (∀ p : Page α, IsRun T (i + f.items.length) p.items → IsRun T i (f.appendPage p).items) ∧
    (∀ k cursor, IsRun T 0 (f.headPage { items := T.take k, cursor }).items) ∧
    (∀ N : List α, IsRun (N ++ T) (N.length + i) f.items)

theorem contiguous : Contiguous α := fun _T hT f _i hF =>
  ⟨run_nodup hT hF, fun _p hp => run_append hF hp, fun _k c => headPage_run hT f hF c,
   fun N => run_grow N hF⟩

end Paged
end CairnAtproto
