import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_411
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_331
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_333
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_335
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_336
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_409
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_410
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_411 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 3 0) 145)) (Sierksma.FB.KS 3 145) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_411
