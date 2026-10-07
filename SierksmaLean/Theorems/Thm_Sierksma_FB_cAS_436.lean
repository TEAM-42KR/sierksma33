import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_436
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_301
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_302
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_315
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_316
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_430
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_434
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_435
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_436 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1403)) (Sierksma.FB.KS 5 1403) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_436
