import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_488
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_232
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_233
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_488 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 148, 641, 1309]) (Sierksma.FB.xa1K 70 155) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_488
