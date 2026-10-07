import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_538
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_175
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_177
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_178
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_536
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_537
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_538 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 301, 725]) (Sierksma.FB.xa1K 25 57) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_538
