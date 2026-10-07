import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_414
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_327
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_328
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_329
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_414 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 148, 882, 983]) (Sierksma.FB.xa2K 56 23) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_414
