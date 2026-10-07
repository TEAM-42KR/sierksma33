import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_387
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_369
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_370
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_387 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 145, 879, 980]) (Sierksma.FB.xa2K 70 22) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_387
