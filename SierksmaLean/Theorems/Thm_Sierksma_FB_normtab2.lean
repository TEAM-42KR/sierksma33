import SierksmaLean.Proofs.Proof_Sierksma_FB_normtab2
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.normtab2 :
    ∀ k < 6, ∀ j < 1855, Nat.testBit (Sierksma.FB.intt 36) j = true →
    j ≠ Sierksma.FB.R1.getD k 0 → Sierksma.FB.L1t (Sierksma.FB.R1.getD k 0) ≤ Sierksma.FB.L1t j →
    Sierksma.FB.validPerm (Sierksma.FB.n2 k j) = true ∧
    (∀ f < 36, Sierksma.FB.tau1 (Sierksma.FB.epOf (Sierksma.FB.n2 k j) f) = Sierksma.FB.tau1 f) ∧
    Sierksma.FB.relIdx (Sierksma.FB.n2 k j) (Sierksma.FB.R1.getD k 0) = Sierksma.FB.R1.getD k 0 ∧
    Sierksma.FB.relIdx (Sierksma.FB.n2 k j) j ∈ Sierksma.FB.rootList k :=
  @proof_Sierksma_FB_normtab2
