import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_672
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_2
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_11
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_17
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_19
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_21
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_653
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_655
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_658
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_661
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_663
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_666
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_669
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_671
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_672 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 4 0) 147)) (Sierksma.FB.KS 4 147) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_672
