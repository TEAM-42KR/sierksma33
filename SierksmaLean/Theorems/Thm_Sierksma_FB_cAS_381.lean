import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_381
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_378
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_379
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_381 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 144)) (Sierksma.FB.KS 4 144) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_381
