import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_632
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_45
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_46
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_50
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_51
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_629
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_630
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_631
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_632 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 471, 1402]) (Sierksma.FB.xa0K 29 135) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_632
