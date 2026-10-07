import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_573
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_122
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_123
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_573 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 471, 577, 1406]) (Sierksma.FB.xa0K 71 111) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_573
