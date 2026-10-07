import SierksmaLean.Proofs.Proof_Sierksma_FB_enormtab
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false

theorem Sierksma.FB.enormtab :
    ∀ f < 36, Sierksma.FB.validPerm (Sierksma.FB.enorm f) = true ∧ Sierksma.FB.epOf (Sierksma.FB.enorm f) f = 35 :=
  @proof_Sierksma_FB_enormtab
