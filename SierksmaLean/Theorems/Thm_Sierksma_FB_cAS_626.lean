import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_626
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_54
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_56
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_57
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_624
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_625
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_626 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 469, 1402]) (Sierksma.FB.xa0K 43 114) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_626
