import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_673
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_0
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_1
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_2
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_673 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 1407)) (Sierksma.FB.KS 4 1407) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_673
