import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_395
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_361
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_362
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_368
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_369
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_375
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_376
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_385
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_388
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_391
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_394
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_395 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 145)) (Sierksma.FB.KS 5 145) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_395
