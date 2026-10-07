import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_648
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_27
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_28
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_33
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_34
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_644
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_647
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_648 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 1403)) (Sierksma.FB.KS 4 1403) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_648
