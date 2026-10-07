import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_579
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_114
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_115
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_118
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_577
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_578
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_579 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 469, 1406]) (Sierksma.FB.xa0K 68 134) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_579
