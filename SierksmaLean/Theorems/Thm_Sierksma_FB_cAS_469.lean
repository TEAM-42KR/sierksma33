import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_469
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_260
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_261
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_263
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_264
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_265
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_466
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_467
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_468
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_469 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 640]) (Sierksma.FB.xa2K 2 36) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_469
