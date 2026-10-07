import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_547
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_164
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_165
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_168
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_545
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_546
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_547 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 473, 1408]) (Sierksma.FB.xa1K 4 139) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_547
