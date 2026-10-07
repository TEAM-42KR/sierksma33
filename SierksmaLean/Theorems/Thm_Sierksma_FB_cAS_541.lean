import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_541
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_172
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_173
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_174
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_175
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_539
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_540
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_541 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 301, 724]) (Sierksma.FB.xa1K 25 56) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_541
