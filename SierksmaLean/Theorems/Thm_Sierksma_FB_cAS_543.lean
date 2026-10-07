import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_543
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_170
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_171
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_172
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_542
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_543 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 301, 723]) (Sierksma.FB.xa1K 25 55) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_543
