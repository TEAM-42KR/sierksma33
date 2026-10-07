import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_514
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_202
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_203
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_514 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 640, 1308]) (Sierksma.FB.xa1K 48 144) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_514
