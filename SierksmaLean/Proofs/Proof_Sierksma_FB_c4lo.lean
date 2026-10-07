import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
import SierksmaLean.Theorems.Thm_Sierksma_FB_k_c4lo
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

theorem proof_Sierksma_FB_c4lo : (∀ g ∈ Sierksma.FB.c4W, g < 76545 ∧ Nat.land (Sierksma.FB.covOf g) (Sierksma.FB.intt 35) = 0) ∧
    ∀ x < 1855, ∃ g ∈ Sierksma.FB.c4W, Nat.testBit (Sierksma.FB.covOf g) x = false := by
  have h := Sierksma.FB.k_c4lo
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro g hg
    have := (List.all_eq_true.mp h2) g hg
    simp only [Bool.and_eq_true] at this
    exact ⟨Nat.blt_eq.mp this.1, Nat.eq_of_beq_eq_true this.2⟩
  · intro x hx
    have := br_allR_spec _ 1855 0 h1 x (Nat.zero_le _) (by omega)
    obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp this
    exact ⟨g, hg, by simpa using hb⟩
