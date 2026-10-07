import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_576
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_118
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_119
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_120
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_123
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_124
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_573
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_574
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_575
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_576 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 471, 1406]) (Sierksma.FB.xa0K 68 135) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_576
