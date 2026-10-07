import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_520
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_196
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_198
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_199
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_200
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_518
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_519
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_520 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 301, 1022]) (Sierksma.FB.xa1K 25 105) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_520
