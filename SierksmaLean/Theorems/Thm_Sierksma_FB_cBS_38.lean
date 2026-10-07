import SierksmaLean.Proofs.Proof_Sierksma_FB_cBS_38
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XB
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_23
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_24
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_25
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cBS_38 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1406)) (Sierksma.FB.KS 5 1406) 5 (Sierksma.FB.capsOf 2 5)) :=
  @proof_Sierksma_FB_cBS_38
