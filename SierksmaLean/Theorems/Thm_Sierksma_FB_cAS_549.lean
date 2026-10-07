import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_549
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_161
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_162
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_163
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_164
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_548
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_549 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 472, 1408]) (Sierksma.FB.xa1K 4 138) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_549
