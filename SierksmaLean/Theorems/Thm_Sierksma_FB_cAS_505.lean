import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_505
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_212
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_215
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_503
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_504
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_505 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 146, 980]) (Sierksma.FB.xa1K 47 78) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_505
