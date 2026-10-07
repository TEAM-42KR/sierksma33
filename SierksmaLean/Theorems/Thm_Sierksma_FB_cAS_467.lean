import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_467
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_262
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_263
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_467 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 640, 1309]) (Sierksma.FB.xa2K 5 165) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_467
