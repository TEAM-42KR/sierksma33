import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_548
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_162
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_163
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_548 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 472, 576, 1408]) (Sierksma.FB.xa1K 9 90) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_548
