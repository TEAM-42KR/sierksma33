import SierksmaLean.Proofs.Proof_Sierksma_FB_finite_core_box_aux
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import Mathlib.Data.Nat.Bitwise
set_option autoImplicit false

theorem Sierksma.FB.finite_core_box_aux :
    (∀ a b i : Nat, Nat.testBit (Sierksma.FB.memBits (Sierksma.FB.pairSort a b)) i = true ↔ i = a ∨ i = b) ∧
  (∀ k : Nat, k < 6 → ∀ r2 ∈ Sierksma.FB.rootList k, Sierksma.FB.R1.getD k 0 ≠ r2) ∧
  ((∀ f : Nat, f < 36 → Sierksma.FB.field (Sierksma.FB.capsOf 15 3) f = 15) ∧
    Sierksma.FB.field (Sierksma.FB.capsOf 15 3) 36 = 3) ∧
  ((∀ f : Nat, f < 36 → Sierksma.FB.field (Sierksma.FB.capsOf 3 4) f = 3) ∧
    Sierksma.FB.field (Sierksma.FB.capsOf 3 4) 36 = 4) ∧
  ((∀ f : Nat, f < 36 → Sierksma.FB.field (Sierksma.FB.capsOf 2 5) f = 2) ∧
    Sierksma.FB.field (Sierksma.FB.capsOf 2 5) 36 = 5) :=
  @proof_Sierksma_FB_finite_core_box_aux
