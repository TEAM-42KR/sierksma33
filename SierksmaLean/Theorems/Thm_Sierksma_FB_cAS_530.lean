import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_530
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_183
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_185
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_186
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_528
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_529
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_530 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 301, 1017]) (Sierksma.FB.xa1K 25 100) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_530
