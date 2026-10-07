import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_516
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_202
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_212
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_218
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_222
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_223
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_498
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_499
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_502
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_505
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_506
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_509
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_512
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_515
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_516 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 146)) (Sierksma.FB.KS 4 146) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_516
