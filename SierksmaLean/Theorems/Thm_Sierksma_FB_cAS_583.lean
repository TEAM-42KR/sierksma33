import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_583
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_109
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_110
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_125
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_126
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_572
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_576
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_579
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_582
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_583 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1406)) (Sierksma.FB.KS 5 1406) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_583
