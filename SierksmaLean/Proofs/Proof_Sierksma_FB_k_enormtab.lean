import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem proof_Sierksma_FB_k_enormtab :
    Sierksma.FB.allR (fun f => Sierksma.FB.validPerm (Sierksma.FB.enorm f) && Nat.beq (Sierksma.FB.epOf (Sierksma.FB.enorm f) f) 35) 0 36 = true := by
  decide +kernel
