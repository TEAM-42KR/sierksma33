import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_435
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_302
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_303
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_304
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_305
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_435 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 468, 1403]) (Sierksma.FB.xa2K 41 133) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_435
