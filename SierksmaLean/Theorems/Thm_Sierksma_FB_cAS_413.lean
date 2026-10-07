import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_413
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_329
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_330
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_412
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_413 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 148, 984]) (Sierksma.FB.xa2K 51 82) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_413
