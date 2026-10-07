import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_531
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_182
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_183
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_531 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 301, 727, 1109]) (Sierksma.FB.xa1K 30 111) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_531
