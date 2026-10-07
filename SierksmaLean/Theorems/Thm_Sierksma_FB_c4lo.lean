import SierksmaLean.Proofs.Proof_Sierksma_FB_c4lo
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false

theorem Sierksma.FB.c4lo :
    (∀ g ∈ Sierksma.FB.c4W, g < 76545 ∧ Nat.land (Sierksma.FB.covOf g) (Sierksma.FB.intt 35) = 0) ∧
    ∀ x < 1855, ∃ g ∈ Sierksma.FB.c4W, Nat.testBit (Sierksma.FB.covOf g) x = false :=
  @proof_Sierksma_FB_c4lo
