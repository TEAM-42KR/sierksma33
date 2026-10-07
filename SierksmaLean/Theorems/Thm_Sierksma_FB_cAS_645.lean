import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_645
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_29
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_30
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_645 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 469, 576, 1403]) (Sierksma.FB.xa0K 23 77) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_645
