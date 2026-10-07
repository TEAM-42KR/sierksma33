import SierksmaLean.Definitions.Def_Sierksma_FBUtil
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem proof_Sierksma_FB_tab_colB2 : Sierksma.FB.allR Sierksma.FB.c3body 9842 4921 = true := by
  decide +kernel
