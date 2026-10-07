import SierksmaLean.Proofs.Proof_Sierksma_FB_cBS_44
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XB
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_5
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_6
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_7
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cBS_44 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 1403)) (Sierksma.FB.KS 4 1403) 5 (Sierksma.FB.capsOf 2 5)) :=
  @proof_Sierksma_FB_cBS_44
