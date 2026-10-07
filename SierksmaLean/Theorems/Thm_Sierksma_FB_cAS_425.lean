import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_425
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_316
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_317
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_318
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_319
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_424
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_425 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 148, 639]) (Sierksma.FB.xa2K 51 35) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_425
