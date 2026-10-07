import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_443
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_291
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_292
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_293
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_443 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 881, 983]) (Sierksma.FB.xa2K 12 23) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_443
