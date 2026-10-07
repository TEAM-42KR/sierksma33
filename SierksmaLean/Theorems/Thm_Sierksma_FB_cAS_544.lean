import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_544
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_170
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_183
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_191
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_200
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_520
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_522
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_524
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_527
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_530
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_532
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_535
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_538
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_541
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_543
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_544 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 301)) (Sierksma.FB.KS 4 301) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_544
