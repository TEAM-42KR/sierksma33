import SierksmaLean.Proofs.Proof_Sierksma_FB_cBS_42
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XB
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_12
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_13
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_14
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cBS_42 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1366)) (Sierksma.FB.KS 5 1366) 5 (Sierksma.FB.capsOf 2 5)) :=
  @proof_Sierksma_FB_cBS_42
