import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_552
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_157
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_160
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_161
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_550
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_551
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_552 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 471, 1408]) (Sierksma.FB.xa1K 4 137) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_552
