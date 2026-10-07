import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_507
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_209
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_210
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_507 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 642, 1313]) (Sierksma.FB.xa1K 50 147) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_507
