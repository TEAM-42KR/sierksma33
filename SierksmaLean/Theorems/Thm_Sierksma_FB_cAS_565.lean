import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_565
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_140
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_168
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_169
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_547
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_549
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_552
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_554
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_559
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_564
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_565 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1408)) (Sierksma.FB.KS 5 1408) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_565
