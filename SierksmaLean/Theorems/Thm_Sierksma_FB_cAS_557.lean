import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_557
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_148
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_149
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_150
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_557 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 468, 573, 1408]) (Sierksma.FB.xa1K 6 88) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_557
