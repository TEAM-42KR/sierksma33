import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_475
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_254
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_277
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_278
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_301
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_439
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_442
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_446
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_447
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_451
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_455
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_458
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_461
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_465
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_469
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_473
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_474
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_475 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 147)) (Sierksma.FB.KS 5 147) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_475
