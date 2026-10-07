import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_138
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_138 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 144, 878, 982]) (Sierksma.FB.xa1K 3 21) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 144, 879, 982]) (Sierksma.FB.xa1K 3 22) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 144, 881, 982]) (Sierksma.FB.xa1K 3 23) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 144, 882, 982]) (Sierksma.FB.xa1K 3 24) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_138
