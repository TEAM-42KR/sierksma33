import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_510
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_206
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_207
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_510 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 641, 1313]) (Sierksma.FB.xa1K 49 147) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_510
