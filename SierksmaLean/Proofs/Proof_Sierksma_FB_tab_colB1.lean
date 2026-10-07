import SierksmaLean.Definitions.Def_Sierksma_FBUtil
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem proof_Sierksma_FB_tab_colB1 : Sierksma.FB.allR Sierksma.FB.c3body 4921 4921 = true := by
  decide +kernel
