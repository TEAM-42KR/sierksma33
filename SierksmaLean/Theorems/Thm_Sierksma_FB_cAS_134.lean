import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_134
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_134 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 144, 638, 1309]) (Sierksma.FB.xa1K 2 135) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 144, 638, 1310]) (Sierksma.FB.xa1K 2 136) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_134
