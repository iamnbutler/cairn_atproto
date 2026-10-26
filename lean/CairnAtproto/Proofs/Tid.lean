module

public import CairnAtproto.Tid
public import CairnAtproto.Proofs.RoundTrip

/-! # TIDs: their text reads back, and a session's strictly increase

* `Tid.decode_encode`: the 13 characters read back as the TID (its time and clock id);
  `Tid.encode_length`, `Tid.encode_chars`: they are 13, each of the alphabet.
* `TidClock.mint_increasing`: a TID minted after another by the same minter is greater (as a
  number, so also as text), and `Minted` (a session's TIDs, newest first) stays strictly
  decreasing from the newest whatever clock readings come (`Minted.mint`). -/

@[expose] public section

namespace CairnAtproto

theorem length_base32Digits : ∀ (w n : Nat), (base32Digits w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [base32Digits, length_base32Digits w]

theorem base32Digits_lt : ∀ (w n : Nat), ∀ d ∈ base32Digits w n, d < 32
  | 0, _, d, h => by simp [base32Digits] at h
  | w + 1, n, d, h => by
    simp only [base32Digits, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact base32Digits_lt w _ d h
    · exact Nat.mod_lt _ (by decide)

theorem ofBase32_append (ds : List Nat) (d : Nat) : ofBase32 (ds ++ [d]) = ofBase32 ds * 32 + d := by
  simp [ofBase32, List.foldl_append]

theorem ofBase32_base32Digits : ∀ (w n : Nat), n < 32 ^ w → ofBase32 (base32Digits w n) = n
  | 0, n, h => by simp at h; subst h; rfl
  | w + 1, n, h => by
    rw [base32Digits, ofBase32_append, ofBase32_base32Digits w (n / 32)
      (Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ] at h; simpa [Nat.mul_comm] using h))]
    omega

theorem tidDigit_tidChar : ∀ d : Fin 32, tidDigit (tidChar d.val) = some d.val := by
  decide +kernel

theorem tidChar_mem : ∀ d : Fin 32, tidChar d.val ∈ tidAlphabet := by
  decide +kernel

theorem optMap_tidDigit (ds : List Nat) (h : ∀ d ∈ ds, d < 32) :
    optMap tidDigit (ds.map tidChar) = some ds :=
  optMap_map tidDigit tidChar ds fun d hd => tidDigit_tidChar ⟨d, h d hd⟩

theorem Tid.toNat_lt (t : Tid) : t.toNat < tidMicrosBound * tidClockBound := by
  have := t.micros_lt; have := t.clock_lt
  simp only [Tid.toNat, tidMicrosBound, tidClockBound] at *
  omega

/-- A TID's text is 13 characters. -/
theorem Tid.encode_length (t : Tid) : t.encode.length = 13 := by
  simp [Tid.encode, length_base32Digits]

/-- Each of them is one of the sortable alphabet's. -/
theorem Tid.encode_chars (t : Tid) : ∀ c ∈ t.encode.toList, c ∈ tidAlphabet := by
  intro c hc
  simp only [Tid.encode, String.toList_ofList, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  exact tidChar_mem ⟨d, base32Digits_lt _ _ d hd⟩

theorem Tid.ofNat?_toNat (t : Tid) : Tid.ofNat? t.toNat = some t := by
  unfold Tid.ofNat?
  rw [dite_eq_left_of_eq_true (eq_true t.toNat_lt)]
  obtain ⟨m, c, hm, hc⟩ := t
  have hc' : c < 1024 := hc
  simp only [Tid.toNat, Option.some.injEq, Tid.mk.injEq, tidClockBound]
  constructor <;> omega

/-- **A TID's text reads back as the TID**: its time and clock id. -/
theorem Tid.decode_encode (t : Tid) : Tid.decode t.encode = some t := by
  have hlt : t.toNat < 32 ^ 13 := Nat.lt_of_lt_of_le t.toNat_lt (by decide)
  simp only [Tid.decode, Tid.encode, String.toList_ofList, List.length_map, length_base32Digits,
    ite_true, optMap_tidDigit _ (base32Digits_lt 13 t.toNat), ofBase32_base32Digits 13 _ hlt,
    Tid.ofNat?_toNat]

/-! ## Minting -/

theorem TidClock.mint_some {g : TidClock} {now : Nat} {t : Tid} {g' : TidClock}
    (h : g.mint now = some (t, g')) :
    t.micros = g.next now ∧ t.clock = g.clock % tidClockBound ∧ g'.last = some t.micros ∧
      g'.clock = g.clock := by
  unfold TidClock.mint at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- **A TID minted after another is greater**: its microseconds are past the last minted, and its
clock id is the minter's. -/
theorem TidClock.mint_increasing {g : TidClock} {now : Nat} {t : Tid} {g' : TidClock}
    (h : g.mint now = some (t, g')) (l : Nat) (hl : g.last = some l) : l < t.micros := by
  obtain ⟨hm, -, -, -⟩ := TidClock.mint_some h
  simp only [hm, TidClock.next, hl]
  omega

/-- The TIDs a minter has minted, newest first: each greater than the ones after it, all with
its clock id, and the newest's microseconds its `last`. -/
def Minted (g : TidClock) (ts : List Tid) : Prop :=
  ts.Pairwise (fun a b => b.toNat < a.toNat) ∧ (∀ t ∈ ts, t.clock = g.clock % tidClockBound) ∧
    g.last = ts.head?.map (·.micros)

instance (g : TidClock) (ts : List Tid) : Decidable (Minted g ts) := by
  unfold Minted; infer_instance

theorem Minted.new (c : Nat) : Minted (TidClock.new c) [] := by
  simp [Minted, TidClock.new]

/-- **Minting keeps `Minted`**: a session's TIDs strictly increase, whatever the clock reads. -/
theorem Minted.mint {g : TidClock} {ts : List Tid} (h : Minted g ts) (now : Nat) :
    match g.mint now with
    | some (t, g') => Minted g' (t :: ts)
    | none => Minted g ts := by
  split
  · next t g' hm =>
    obtain ⟨hmic, hclk, hlast, hg⟩ := TidClock.mint_some hm
    obtain ⟨hp, hc, hl⟩ := h
    refine ⟨List.pairwise_cons.2 ⟨fun b hb => ?_, hp⟩, ?_, by simp [hlast]⟩
    · -- b is at most the newest, whose micros are below t's
      have hb' : b.micros ≤ (ts.head?.map (·.micros)).getD 0 := by
        cases ts with
        | nil => simp at hb
        | cons x xs =>
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · simp
          · have := (List.pairwise_cons.1 hp).1 b hb
            have e1 := hc x (List.mem_cons_self ..)
            have e2 := hc b (List.mem_cons_of_mem _ hb)
            simp only [Tid.toNat] at this
            simp only [List.head?_cons, Option.map_some, Option.getD_some]
            have := b.clock_lt; have := x.clock_lt
            simp only [tidClockBound] at *
            omega
      cases ts with
      | nil => simp at hb
      | cons x xs =>
        have hl' : g.last = some x.micros := by simpa using hl
        have := TidClock.mint_increasing hm x.micros hl'
        simp only [List.head?_cons, Option.map_some, Option.getD_some] at hb'
        have e1 := hc b hb
        simp only [Tid.toNat, hmic] at *
        have hmic' := TidClock.mint_some hm
        have := t.clock_lt
        rw [hclk, ← e1]
        have : b.micros < t.micros := by omega
        simp only [tidClockBound] at *
        omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [hclk, hg]
      · rw [hg]; exact hc x hx
  · exact h

end CairnAtproto
