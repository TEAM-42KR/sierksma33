import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_498
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_219
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_220
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_222
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_496
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_497
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_498 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 985]) (Sierksma.FB.xa1K 47 83) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_498
