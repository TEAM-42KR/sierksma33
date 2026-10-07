import SierksmaLean.Proofs.Proof_Sierksma_public_iff
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
set_option autoImplicit false
open scoped BigOperators
open Common

theorem Sierksma.public_iff :
    (∀ p : Fin 9 → EuclideanSpace ℝ (Fin 3),
      8 ≤ Nat.card {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
        Q.parts.card = 3 ∧
          (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty}) ↔
    ∀ P : Config 9 3, 8 ≤ TverbergCount 3 P :=
  @proof_Sierksma_public_iff
