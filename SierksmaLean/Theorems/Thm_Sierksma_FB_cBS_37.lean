import SierksmaLean.Proofs.Proof_Sierksma_FB_cBS_37
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XB
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_25
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_26
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_27
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_28
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_29
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_30
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_31
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_32
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_33
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_34
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_35
import SierksmaLean.Theorems.Thm_Sierksma_FB_cBS_36
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cBS_37 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1408)) (Sierksma.FB.KS 5 1408) 5 (Sierksma.FB.capsOf 2 5)) :=
  @proof_Sierksma_FB_cBS_37
