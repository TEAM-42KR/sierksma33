import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_620
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_61
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_62
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_73
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_84
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_607
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_608
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_610
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_611
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_612
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_613
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_614
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_615
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_616
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_617
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_618
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_619
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_620 :
    (Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD 3 0) 148)) (Sierksma.FB.KS 3 148) 5 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_620
