import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import Mathlib.Data.Nat.Bitwise
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
theorem proof_Sierksma_FB_finite_core_box_aux :
  (∀ a b i : Nat, Nat.testBit (Sierksma.FB.memBits (Sierksma.FB.pairSort a b)) i = true ↔ i = a ∨ i = b) ∧
  (∀ k : Nat, k < 6 → ∀ r2 ∈ Sierksma.FB.rootList k, Sierksma.FB.R1.getD k 0 ≠ r2) ∧
  ((∀ f : Nat, f < 36 → Sierksma.FB.field (Sierksma.FB.capsOf 15 3) f = 15) ∧
    Sierksma.FB.field (Sierksma.FB.capsOf 15 3) 36 = 3) ∧
  ((∀ f : Nat, f < 36 → Sierksma.FB.field (Sierksma.FB.capsOf 3 4) f = 3) ∧
    Sierksma.FB.field (Sierksma.FB.capsOf 3 4) 36 = 4) ∧
  ((∀ f : Nat, f < 36 → Sierksma.FB.field (Sierksma.FB.capsOf 2 5) f = 2) ∧
    Sierksma.FB.field (Sierksma.FB.capsOf 2 5) 36 = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b i
    cases h : Nat.blt a b <;>
      simp only [Sierksma.FB.pairSort, h, Bool.cond_true, Bool.cond_false,
        Sierksma.FB.memBits, List.foldr_cons, List.foldr_nil]
    all_goals
      simp only [Nat.lor_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.or_zero,
        Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
      tauto
  · have hroot : ∀ k : Fin 6, Sierksma.FB.R1.getD k.val 0 ∉ Sierksma.FB.rootList k.val := by
      decide
    intro k hk r2 hr heq
    apply hroot ⟨k, hk⟩
    rw [heq]
    exact hr
  · constructor
    · have hc : ∀ f : Fin 36, Sierksma.FB.field (Sierksma.FB.capsOf 15 3) f.val = 15 := by decide
      intro f hf
      exact hc ⟨f, hf⟩
    · decide
  · constructor
    · have hc : ∀ f : Fin 36, Sierksma.FB.field (Sierksma.FB.capsOf 3 4) f.val = 3 := by decide
      intro f hf
      exact hc ⟨f, hf⟩
    · decide
  · constructor
    · have hc : ∀ f : Fin 36, Sierksma.FB.field (Sierksma.FB.capsOf 2 5) f.val = 2 := by decide
      intro f hf
      exact hc ⟨f, hf⟩
    · decide
