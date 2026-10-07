import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_580
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_112
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_113
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_114
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_580 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 468, 577, 1406]) (Sierksma.FB.xa0K 69 111) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_580
