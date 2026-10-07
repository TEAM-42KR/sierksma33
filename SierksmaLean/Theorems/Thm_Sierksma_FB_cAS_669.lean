import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_669
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_4
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_5
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_6
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_667
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_668
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_669 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 147, 640]) (Sierksma.FB.xa0K 1 36) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_669
