import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_418
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_324
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_326
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_416
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_417
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_418 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 148, 981]) (Sierksma.FB.xa2K 51 79) 4 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_418
