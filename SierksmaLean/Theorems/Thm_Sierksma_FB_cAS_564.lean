import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_564
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_140
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_142
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_143
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_146
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_147
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_560
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_561
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_562
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_563
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_564 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 467, 1408]) (Sierksma.FB.xa1K 4 134) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_564
