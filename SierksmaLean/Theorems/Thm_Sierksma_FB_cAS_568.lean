import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_568
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_133
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_136
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_137
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_139
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_140
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_566
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_567
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_568 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 5 0) 144)) (Sierksma.FB.KS 5 144) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_568
