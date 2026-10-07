import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_255
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_255 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1310]) (Sierksma.FB.xa2K 3 166) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1311]) (Sierksma.FB.xa2K 3 167) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1312]) (Sierksma.FB.xa2K 3 168) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1313]) (Sierksma.FB.xa2K 3 169) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1320]) (Sierksma.FB.xa2K 3 170) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1321]) (Sierksma.FB.xa2K 3 171) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1322]) (Sierksma.FB.xa2K 3 172) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1323]) (Sierksma.FB.xa2K 3 173) 3 (Sierksma.FB.capsOf 3 4)) ∧ (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 638, 1324]) (Sierksma.FB.xa2K 3 174) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_255
