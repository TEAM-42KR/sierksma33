import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_393
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_363
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_364
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_393 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 145, 640, 1308]) (Sierksma.FB.xa2K 68 144) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_393
