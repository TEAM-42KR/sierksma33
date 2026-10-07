import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_495
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_223
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_237
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_251
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_477
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_480
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_481
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_484
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_485
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_486
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_489
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_490
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_493
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_494
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_495 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 148)) (Sierksma.FB.KS 5 148) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_495
