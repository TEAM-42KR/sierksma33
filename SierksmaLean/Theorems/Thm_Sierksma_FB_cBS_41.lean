import SierksmaLean.Proofs.Proof_Sierksma_FB_cBS_41
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XB
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_15
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_16
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_17
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_18
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cBS_41 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1396)) (Sierksma.FB.KS 5 1396) 5 (Sierksma.FB.capsOf 2 5)) :=
  @proof_Sierksma_FB_cBS_41
