import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_562
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_142
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_143
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_562 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 467, 573, 1408]) (Sierksma.FB.xa1K 5 88) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_562
