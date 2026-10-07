import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_420
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_322
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_323
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_419
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_420 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 148, 643]) (Sierksma.FB.xa2K 51 39) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_420
