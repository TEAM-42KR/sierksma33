import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_644
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_30
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_31
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_33
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_642
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_643
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_644 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 472, 1403]) (Sierksma.FB.xa0K 22 119) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_644
