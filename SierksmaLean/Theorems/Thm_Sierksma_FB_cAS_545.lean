import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_545
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_166
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_167
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_168
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_545 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 473, 577, 1408]) (Sierksma.FB.xa1K 10 91) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_545
