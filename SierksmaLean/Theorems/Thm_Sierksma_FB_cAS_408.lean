import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_408
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_336
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_337
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_350
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_361
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_396
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_397
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_399
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_400
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_401
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_402
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_404
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_405
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_406
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_407
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_408 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 3 0) 147)) (Sierksma.FB.KS 3 147) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_408
