import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_238
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_238 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 148, 877, 980]) (Sierksma.FB.xa1K 71 20) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 148, 878, 980]) (Sierksma.FB.xa1K 71 21) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 148, 879, 980]) (Sierksma.FB.xa1K 71 22) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 148, 881, 980]) (Sierksma.FB.xa1K 71 23) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 148, 882, 980]) (Sierksma.FB.xa1K 71 24) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_238
