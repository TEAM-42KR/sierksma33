import SierksmaLean.Proofs.Proof_Sierksma_FB_covOf_spec
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.covOf_spec :
    (∀ g < 76545, Sierksma.ValidConstraint 3 (Sierksma.FB.constraintOf g)) ∧
    (∀ q : Sierksma.PairConstraint 9, Sierksma.ValidConstraint 3 q → ∃ g < 76545, Sierksma.FB.constraintOf g = q) ∧
    (∀ g < 76545, ∀ i < 1855,
      Nat.testBit (Sierksma.FB.covOf g) i = true ↔ Sierksma.Covers (Sierksma.FB.partOf i) (Sierksma.FB.constraintOf g)) :=
  @proof_Sierksma_FB_covOf_spec
