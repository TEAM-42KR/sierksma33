import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_584
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_106
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_107
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_584 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 472, 571, 1404]) (Sierksma.FB.xa0K 66 94) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_584
