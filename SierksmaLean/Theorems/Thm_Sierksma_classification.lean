import SierksmaLean.Proofs.Proof_Sierksma_classification
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_Amplification
import SierksmaLean.Definitions.Def_Sierksma_FractionalCover
import SierksmaLean.Definitions.Def_Sierksma_TwistedRealization
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
set_option maxRecDepth 4000

theorem Sierksma.classification :
    ∀ (P : Config 9 3) (hP : StrongGP P) (Q : Common.Partition 9) (hQ : BlocksOn Q (Q.biUnion id)) (hcard : Q.card = 3) (hz : HasCommonHull P Q), Q ∈ Universe 3 :=
  @proof_Sierksma_classification
