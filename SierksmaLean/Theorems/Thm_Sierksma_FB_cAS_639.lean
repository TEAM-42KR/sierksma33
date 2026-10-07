import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_639
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_35
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_36
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_639 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 467, 573, 1402]) (Sierksma.FB.xa0K 30 108) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_639
