import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_622
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_57
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_58
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_59
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_622 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 472, 573, 1402]) (Sierksma.FB.xa0K 45 96) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_622
