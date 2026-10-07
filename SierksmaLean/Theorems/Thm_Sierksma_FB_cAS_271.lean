import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_271
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_271 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 642, 1308]) (Sierksma.FB.xa2K 7 164) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 642, 1309]) (Sierksma.FB.xa2K 7 165) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_271
