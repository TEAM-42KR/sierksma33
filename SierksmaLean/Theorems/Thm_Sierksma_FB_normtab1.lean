import SierksmaLean.Proofs.Proof_Sierksma_FB_normtab1
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.normtab1 :
    ∀ j < 1855, Nat.testBit (Sierksma.FB.intt 36) j = true →
    Sierksma.FB.validPerm (Sierksma.FB.n1 j) = true ∧
    (∀ f < 36, Sierksma.FB.tau1 (Sierksma.FB.epOf (Sierksma.FB.n1 j) f) = Sierksma.FB.tau1 f) ∧
    ∃ k < 6, Sierksma.FB.relIdx (Sierksma.FB.n1 j) j = Sierksma.FB.R1.getD k 0 :=
  @proof_Sierksma_FB_normtab1
