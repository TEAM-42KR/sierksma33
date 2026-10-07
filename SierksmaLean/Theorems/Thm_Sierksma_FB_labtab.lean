import SierksmaLean.Proofs.Proof_Sierksma_FB_labtab
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false

theorem Sierksma.FB.labtab :
    ∀ j < 1855, Sierksma.FB.L1t j = Sierksma.FB.lab Sierksma.FB.tau1 j ∧
    ∀ k < 6, Sierksma.FB.L2t k j = Sierksma.FB.lab (Sierksma.FB.tau2 (Sierksma.FB.R1.getD k 0)) j :=
  @proof_Sierksma_FB_labtab
