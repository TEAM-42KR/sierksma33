import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_635
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_41
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_42
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_43
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_44
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_45
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_633
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_634
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_635 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [65, 469, 1402]) (Sierksma.FB.xa0K 29 134) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_635
