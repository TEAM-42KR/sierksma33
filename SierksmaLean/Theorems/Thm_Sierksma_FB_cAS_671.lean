import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_671
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_2
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_3
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_4
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_670
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_671 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 147, 639]) (Sierksma.FB.xa0K 1 35) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_671
