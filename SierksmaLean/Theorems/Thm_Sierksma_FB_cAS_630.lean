import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_630
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_47
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_48
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_49
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_630 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 471, 575, 1402]) (Sierksma.FB.xa0K 33 109) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_630
