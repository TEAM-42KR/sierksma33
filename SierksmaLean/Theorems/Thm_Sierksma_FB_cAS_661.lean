import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_661
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_11
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_12
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_14
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_659
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_660
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_661 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 147, 980]) (Sierksma.FB.xa0K 1 78) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_661
