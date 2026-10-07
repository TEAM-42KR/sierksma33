import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_426
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_316
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_319
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_322
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_323
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_324
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_327
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_331
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_413
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_415
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_418
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_420
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_423
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_425
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_426 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 148)) (Sierksma.FB.KS 4 148) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_426
