import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_448
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_284
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_285
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_286
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_448 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 881, 981]) (Sierksma.FB.xa2K 10 23) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_448
