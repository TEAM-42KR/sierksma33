import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_524
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_191
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_193
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_194
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_523
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_524 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 301, 1020]) (Sierksma.FB.xa1K 25 103) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_524
