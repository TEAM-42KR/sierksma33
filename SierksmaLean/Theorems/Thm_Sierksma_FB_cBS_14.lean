import SierksmaLean.Proofs.Proof_Sierksma_FB_cBS_14
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XB
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cBS_14 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 859, 1366]) (Sierksma.FB.xbK 3 219) 4 (Sierksma.FB.capsOf 2 5)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 860, 1366]) (Sierksma.FB.xbK 3 220) 4 (Sierksma.FB.capsOf 2 5)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 861, 1366]) (Sierksma.FB.xbK 3 221) 4 (Sierksma.FB.capsOf 2 5)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 862, 1366]) (Sierksma.FB.xbK 3 222) 4 (Sierksma.FB.capsOf 2 5)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 863, 1366]) (Sierksma.FB.xbK 3 223) 4 (Sierksma.FB.capsOf 2 5)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1368)) (Sierksma.FB.KS 5 1368) 5 (Sierksma.FB.capsOf 2 5)) :=
  @proof_Sierksma_FB_cBS_14
