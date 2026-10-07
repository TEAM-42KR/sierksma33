import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_559
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_147
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_153
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_154
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_555
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_556
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_557
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_558
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_559 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 468, 1408]) (Sierksma.FB.xa1K 4 135) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_559
