import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_461
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_270
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_271
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_272
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_273
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_274
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_459
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_460
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_461 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 642]) (Sierksma.FB.xa2K 2 38) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_461
