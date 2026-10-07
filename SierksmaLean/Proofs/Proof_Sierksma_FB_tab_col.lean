import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col_a0
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col_a1
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col_a2
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col_a3
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col_c
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colB0
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colD0
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colB1
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colD1
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colB2
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colD2
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colB3
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_colD3
set_option autoImplicit false

theorem tc_allR_spec (f : ℕ → Bool) : ∀ (n lo : ℕ), Sierksma.FB.allR f lo n = true →
    ∀ k, lo ≤ k → k < lo + n → f k = true := by
  intro n
  induction n with
  | zero => intro lo _ k h1 h2; omega
  | succ n ih =>
    intro lo h k h1 h2
    have e : Sierksma.FB.allR f lo (n+1) = (f lo && Sierksma.FB.allR f (lo+1) n) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with h3 | h3
    · subst h3; exact h.1
    · exact ih (lo+1) h.2 k (by omega) (by omega)

theorem tc_allR_of (f : ℕ → Bool) : ∀ (n lo : ℕ), (∀ k, lo ≤ k → k < lo + n → f k = true) →
    Sierksma.FB.allR f lo n = true := by
  intro n
  induction n with
  | zero => intro lo _; rfl
  | succ n ih =>
    intro lo h
    have e : Sierksma.FB.allR f lo (n+1) = (f lo && Sierksma.FB.allR f (lo+1) n) := rfl
    rw [e, Bool.and_eq_true]
    exact ⟨h lo (Nat.le_refl _) (by omega), ih (lo+1) (fun k h1 h2 => h k (by omega) (by omega))⟩

theorem tc_anyR_of (f : ℕ → Bool) : ∀ (n lo k : ℕ), lo ≤ k → k < lo + n → f k = true →
    Sierksma.FB.anyR f lo n = true := by
  intro n
  induction n with
  | zero => intro lo k h1 h2 _; omega
  | succ n ih =>
    intro lo k h1 h2 hk
    have e : Sierksma.FB.anyR f lo (n+1) = (f lo || Sierksma.FB.anyR f (lo+1) n) := rfl
    rw [e, Bool.or_eq_true]
    rcases Nat.eq_or_lt_of_le h1 with h3 | h3
    · subst h3; exact Or.inl hk
    · exact Or.inr (ih (lo+1) k (by omega) (by omega) hk)

theorem tc_beq_iff (x y z w : ℕ) (h : (Nat.beq x y == Nat.beq z w) = true) : (x = y ↔ z = w) := by
  have h2 : Nat.beq x y = Nat.beq z w := beq_iff_eq.mp h
  constructor
  · intro e; subst e; rw [Nat.beq_refl] at h2; exact Nat.eq_of_beq_eq_true h2.symm
  · intro e; subst e; rw [Nat.beq_refl] at h2; exact Nat.eq_of_beq_eq_true h2

theorem tc_c3 (code : ℕ) (hc : code < 19683) : Sierksma.FB.c3body code = true := by
  by_cases k0 : code < 4921
  · exact tc_allR_spec _ 4921 0 Sierksma.FB.tab_colB0 code (Nat.zero_le _) (by omega)
  by_cases k1 : code < 9842
  · exact tc_allR_spec _ 4921 4921 Sierksma.FB.tab_colB1 code (by omega) (by omega)
  by_cases k2 : code < 14763
  · exact tc_allR_spec _ 4921 9842 Sierksma.FB.tab_colB2 code (by omega) (by omega)
  · exact tc_allR_spec _ 4920 14763 Sierksma.FB.tab_colB3 code (by omega) (by omega)

theorem tc_c4 (code : ℕ) (hc : code < 19683) : Sierksma.FB.c4body code = true := by
  by_cases k0 : code < 4921
  · exact tc_allR_spec _ 4921 0 Sierksma.FB.tab_colD0 code (Nat.zero_le _) (by omega)
  by_cases k1 : code < 9842
  · exact tc_allR_spec _ 4921 4921 Sierksma.FB.tab_colD1 code (by omega) (by omega)
  by_cases k2 : code < 14763
  · exact tc_allR_spec _ 4921 9842 Sierksma.FB.tab_colD2 code (by omega) (by omega)
  · exact tc_allR_spec _ 4920 14763 Sierksma.FB.tab_colD3 code (by omega) (by omega)

theorem proof_Sierksma_FB_tab_col :
    (∀ i < 1855, Sierksma.FB.colWord i < 262144 ∧ (∀ v < 9, Sierksma.FB.colOf i v < 3) ∧
      Sierksma.FB.colOf i 0 = 0 ∧
      (∀ v < 9, ∀ c < 3, Sierksma.FB.colOf i v = c → 0 < c → ∃ w < v, Sierksma.FB.colOf i w + 1 = c) ∧
      (∀ c < 3, ∃ v < 9, Sierksma.FB.colOf i v = c) ∧
      (∀ c < 3, ((List.range 9).filter (fun v => Nat.beq (Sierksma.FB.colOf i v) c)).length ≤ 4)) ∧
    (∀ i < 1855, Sierksma.FB.idxOf
      (List.foldr (fun v acc => Sierksma.FB.colOf i v * 3 ^ v + acc) 0 (List.range 9)) = i) ∧
    (∀ code < 19683, Sierksma.FB.idxOf code < 1855 → ∀ u < 9, ∀ v < 9,
      (Sierksma.FB.digit3 code u = Sierksma.FB.digit3 code v ↔
        Sierksma.FB.colOf (Sierksma.FB.idxOf code) u = Sierksma.FB.colOf (Sierksma.FB.idxOf code) v)) ∧
    (∀ code < 19683, (∀ c < 3, ∃ v < 9, Sierksma.FB.digit3 code v = c) →
      (∀ c < 3, ((List.range 9).filter (fun v => Nat.beq (Sierksma.FB.digit3 code v) c)).length ≤ 4) →
      Sierksma.FB.idxOf code < 1855) := by
  refine ⟨?_, Sierksma.FB.tab_col_c, ?_, ?_⟩
  · intro i hi
    by_cases k0 : i < 464
    · exact Sierksma.FB.tab_col_a0 i hi (Nat.zero_le _) k0
    by_cases k1 : i < 928
    · exact Sierksma.FB.tab_col_a1 i hi (by omega) k1
    by_cases k2 : i < 1392
    · exact Sierksma.FB.tab_col_a2 i hi (by omega) k2
    · exact Sierksma.FB.tab_col_a3 i hi (by omega) hi
  · intro code hc hi u hu v hv
    have h := tc_c3 code hc
    have hb : Nat.blt (Sierksma.FB.idxOf code) 1855 = true := Nat.blt_eq.mpr hi
    unfold Sierksma.FB.c3body at h
    rw [hb, Bool.not_true, Bool.false_or] at h
    have hu' := tc_allR_spec _ 9 0 h u (Nat.zero_le _) (by omega)
    have hv' := tc_allR_spec _ 9 0 hu' v (Nat.zero_le _) (by omega)
    exact tc_beq_iff _ _ _ _ hv'
  · intro code hc h1 h2
    have h := tc_c4 code hc
    have hA : Sierksma.FB.allR (fun c => Sierksma.FB.anyR (fun v => Nat.beq (Sierksma.FB.digit3 code v) c) 0 9) 0 3 = true := by
      apply tc_allR_of _ 3 0
      intro c _ hc3
      obtain ⟨v, hv9, hv⟩ := h1 c (by omega)
      exact tc_anyR_of _ 9 0 v (Nat.zero_le _) (by omega) (by rw [hv]; exact Nat.beq_refl c)
    have hB : Sierksma.FB.allR (fun c => Nat.ble ((List.range 9).filter (fun v => Nat.beq (Sierksma.FB.digit3 code v) c)).length 4) 0 3 = true := by
      apply tc_allR_of _ 3 0
      intro c _ hc3
      exact Nat.ble_eq.mpr (h2 c (by omega))
    unfold Sierksma.FB.c4body at h
    rw [hA, hB, Bool.and_true, Bool.not_true, Bool.false_or] at h
    exact Nat.blt_eq.mp h
