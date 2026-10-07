import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_211
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_211 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 643, 1304]) (Sierksma.FB.xa1K 51 141) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 643, 1305]) (Sierksma.FB.xa1K 51 142) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 643, 1306]) (Sierksma.FB.xa1K 51 143) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 643, 1308]) (Sierksma.FB.xa1K 51 144) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 643, 1310]) (Sierksma.FB.xa1K 51 145) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 643, 1311]) (Sierksma.FB.xa1K 51 146) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_211
