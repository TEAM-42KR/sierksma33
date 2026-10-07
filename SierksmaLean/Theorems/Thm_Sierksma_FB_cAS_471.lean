import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_471
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_257
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_258
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_471 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 639, 1309]) (Sierksma.FB.xa2K 4 165) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_471
