import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_440
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_295
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_296
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_440 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 883, 984]) (Sierksma.FB.xa2K 13 25) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_440
