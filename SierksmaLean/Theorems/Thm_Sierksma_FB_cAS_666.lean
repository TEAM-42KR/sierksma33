import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_666
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_6
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_7
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_8
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_9
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_664
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_665
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_666 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 147, 641]) (Sierksma.FB.xa0K 1 37) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_666
