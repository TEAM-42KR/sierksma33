import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_normtab2_0
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_normtab2_1
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_normtab2_2
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_normtab2_3
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_normtab2_4
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_normtab2_5
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_rootlink
set_option autoImplicit false
open Sierksma.FB

private theorem br_allR_spec (f : ℕ → Bool) : ∀ (n lo : ℕ), Sierksma.FB.allR f lo n = true →
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

private theorem br_anyR_spec (f : ℕ → Bool) : ∀ (n lo : ℕ), Sierksma.FB.anyR f lo n = true →
    ∃ k, lo ≤ k ∧ k < lo + n ∧ f k = true := by
  intro n
  induction n with
  | zero =>
    intro lo h
    have e : Sierksma.FB.anyR f lo 0 = false := rfl
    rw [e] at h; cases h
  | succ n ih =>
    intro lo h
    have e : Sierksma.FB.anyR f lo (n+1) = (f lo || Sierksma.FB.anyR f (lo+1) n) := rfl
    rw [e, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨lo, Nat.le_refl _, by omega, h⟩
    · obtain ⟨k, h1, h2, h3⟩ := ih (lo+1) h
      exact ⟨k, by omega, by omega, h3⟩

theorem br_nt2 (K : ℕ) (hc : Sierksma.FB.allR (fun j => !(Nat.testBit (Sierksma.FB.intt 36) j) || Nat.beq j (Sierksma.FB.R1.getD K 0) || !(Nat.ble (Sierksma.FB.L1t (Sierksma.FB.R1.getD K 0)) (Sierksma.FB.L1t j)) || (Sierksma.FB.validPerm (Sierksma.FB.n2 K j) && Sierksma.FB.allR (fun f => Nat.beq (Sierksma.FB.tau1 (Sierksma.FB.epOf (Sierksma.FB.n2 K j) f)) (Sierksma.FB.tau1 f)) 0 36 && Nat.beq (Sierksma.FB.relIdx (Sierksma.FB.n2 K j) (Sierksma.FB.R1.getD K 0)) (Sierksma.FB.R1.getD K 0) && Nat.blt (Sierksma.FB.relIdx (Sierksma.FB.n2 K j) j) 1855 && Nat.testBit (Sierksma.FB.rootBits K) (Sierksma.FB.relIdx (Sierksma.FB.n2 K j) j))) 0 1855 = true)
    (hK : K < 6) (j : ℕ) (hj : j < 1855) (hs : Nat.testBit (Sierksma.FB.intt 36) j = true)
    (hne : j ≠ Sierksma.FB.R1.getD K 0) (hle : Sierksma.FB.L1t (Sierksma.FB.R1.getD K 0) ≤ Sierksma.FB.L1t j) :
    Sierksma.FB.validPerm (Sierksma.FB.n2 K j) = true ∧
    (∀ f < 36, Sierksma.FB.tau1 (Sierksma.FB.epOf (Sierksma.FB.n2 K j) f) = Sierksma.FB.tau1 f) ∧
    Sierksma.FB.relIdx (Sierksma.FB.n2 K j) (Sierksma.FB.R1.getD K 0) = Sierksma.FB.R1.getD K 0 ∧
    Sierksma.FB.relIdx (Sierksma.FB.n2 K j) j ∈ Sierksma.FB.rootList K := by
  have h1 := br_allR_spec _ 1855 0 hc j (Nat.zero_le _) (by omega)
  have hne' : Nat.beq j (Sierksma.FB.R1.getD K 0) = false := by
    cases h : Nat.beq j (Sierksma.FB.R1.getD K 0)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hne
  have hle' : Nat.ble (Sierksma.FB.L1t (Sierksma.FB.R1.getD K 0)) (Sierksma.FB.L1t j) = true := Nat.ble_eq.mpr hle
  simp only [hs, hne', hle', Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨hv, ht⟩, hfix⟩, hlt⟩, hbit⟩ := h1
  have link := br_allR_spec _ 6 0 Sierksma.FB.k_rootlink K (Nat.zero_le _) (by omega)
  have hlt' := Nat.blt_eq.mp hlt
  have l2 := br_allR_spec _ 1855 0 link (Sierksma.FB.relIdx (Sierksma.FB.n2 K j) j) (Nat.zero_le _) (by omega)
  simp only [hbit, Bool.not_true, Bool.false_or, List.any_eq_true] at l2
  obtain ⟨r, hr, hre⟩ := l2
  refine ⟨hv, fun f hf => Nat.eq_of_beq_eq_true (br_allR_spec _ 36 0 ht f (Nat.zero_le _) (by omega)), Nat.eq_of_beq_eq_true hfix, ?_⟩
  have e := Nat.eq_of_beq_eq_true hre
  rw [← e]; exact hr

theorem proof_Sierksma_FB_normtab2 : ∀ k < 6, ∀ j < 1855, Nat.testBit (Sierksma.FB.intt 36) j = true →
    j ≠ Sierksma.FB.R1.getD k 0 → Sierksma.FB.L1t (Sierksma.FB.R1.getD k 0) ≤ Sierksma.FB.L1t j →
    Sierksma.FB.validPerm (Sierksma.FB.n2 k j) = true ∧
    (∀ f < 36, Sierksma.FB.tau1 (Sierksma.FB.epOf (Sierksma.FB.n2 k j) f) = Sierksma.FB.tau1 f) ∧
    Sierksma.FB.relIdx (Sierksma.FB.n2 k j) (Sierksma.FB.R1.getD k 0) = Sierksma.FB.R1.getD k 0 ∧
    Sierksma.FB.relIdx (Sierksma.FB.n2 k j) j ∈ Sierksma.FB.rootList k := by
  intro k hk j hj hs hne hle
  interval_cases k
  · exact br_nt2 0 Sierksma.FB.k_normtab2_0 (by decide) j hj hs hne hle
  · exact br_nt2 1 Sierksma.FB.k_normtab2_1 (by decide) j hj hs hne hle
  · exact br_nt2 2 Sierksma.FB.k_normtab2_2 (by decide) j hj hs hne hle
  · exact br_nt2 3 Sierksma.FB.k_normtab2_3 (by decide) j hj hs hne hle
  · exact br_nt2 4 Sierksma.FB.k_normtab2_4 (by decide) j hj hs hne hle
  · exact br_nt2 5 Sierksma.FB.k_normtab2_5 (by decide) j hj hs hne hle
