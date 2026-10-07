import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_654
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_17
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_18
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_654 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 147, 882, 983]) (Sierksma.FB.xa0K 8 23) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_654
