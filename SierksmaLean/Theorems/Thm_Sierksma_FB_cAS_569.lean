import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_569
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_129
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_130
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_131
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_569 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 302, 1018]) (Sierksma.FB.xa1K 0 97) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_569
