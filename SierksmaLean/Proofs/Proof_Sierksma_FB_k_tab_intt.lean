import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem proof_Sierksma_FB_k_tab_intt :
    Sierksma.FB.allR (fun i => Sierksma.FB.allR (fun f => (Nat.testBit (Sierksma.FB.intt f) i == Nat.beq (Sierksma.FB.colOf i (Sierksma.FB.eu f)) (Sierksma.FB.colOf i (Sierksma.FB.ev f)))) 0 36) 0 1855 = true := by
  decide +kernel
