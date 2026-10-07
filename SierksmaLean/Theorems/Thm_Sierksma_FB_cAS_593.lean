import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_593
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_97
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_98
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_101
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_104
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_105
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_589
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_592
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_593 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 145)) (Sierksma.FB.KS 4 145) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_593
