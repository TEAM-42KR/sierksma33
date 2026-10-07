import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_641
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_34
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_51
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_53
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_54
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_628
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_632
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_635
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_638
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_640
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_641 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 1402)) (Sierksma.FB.KS 5 1402) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_641
