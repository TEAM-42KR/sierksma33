import SierksmaLean.Proofs.Proof_Sierksma_FB_k_labtab
import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.k_labtab :
    Sierksma.FB.allR (fun j => Nat.beq (Sierksma.FB.L1t j) (Sierksma.FB.lab Sierksma.FB.tau1 j) && Sierksma.FB.allR (fun k => Nat.beq (Sierksma.FB.L2t k j) (Sierksma.FB.lab (Sierksma.FB.tau2 (Sierksma.FB.R1.getD k 0)) j)) 0 6) 0 1855 = true :=
  @proof_Sierksma_FB_k_labtab
