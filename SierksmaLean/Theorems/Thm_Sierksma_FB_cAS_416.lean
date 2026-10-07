import SierksmaLean.Proofs.Proof_Sierksma_FB_cAS_416
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
import SierksmaLean.Definitions.Def_Sierksma_XA0
import SierksmaLean.Definitions.Def_Sierksma_XA1
import SierksmaLean.Definitions.Def_Sierksma_XA2
import SierksmaLean.Theorems.Thm_Sierksma_FB_run_sound
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_325
import SierksmaLean.Theorems.Thm_Sierksma_FB_cAS_326
set_option autoImplicit false
set_option maxRecDepth 100000

theorem Sierksma.FB.cAS_416 :
    (Sierksma.FB.Good (Sierksma.FB.memBits [61, 148, 882, 981]) (Sierksma.FB.xa2K 55 23) 3 (Sierksma.FB.capsOf 3 4)) :=
  @proof_Sierksma_FB_cAS_416
