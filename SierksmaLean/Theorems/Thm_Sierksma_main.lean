import SierksmaLean.Proofs.Proof_Sierksma_main
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_Amplification
import SierksmaLean.Definitions.Def_Sierksma_FractionalCover
import SierksmaLean.Definitions.Def_Sierksma_TwistedRealization
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
set_option maxRecDepth 4000

theorem Sierksma.main :
    ∀ (P : Config 9 3), 8 ≤ TverbergCount 3 P :=
  @proof_Sierksma_main
