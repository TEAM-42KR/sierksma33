import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_437
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_299
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_300
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_437 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 147, 882, 985]) (Sierksma.FB.xa2K 14 24) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_437
