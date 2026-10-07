import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_558
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_147
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_148
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_558 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 468, 572, 1408]) (Sierksma.FB.xa1K 6 87) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_558
