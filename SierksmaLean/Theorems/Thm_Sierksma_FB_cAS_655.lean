import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_655
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_17
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_18
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_19
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_654
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_655 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 147, 983]) (Sierksma.FB.xa0K 1 81) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_655
