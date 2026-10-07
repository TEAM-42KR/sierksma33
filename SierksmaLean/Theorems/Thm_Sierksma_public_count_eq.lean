import SierksmaLean.Proofs.Proof_Sierksma_public_count_eq
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
set_option autoImplicit false
open scoped BigOperators
open Common

theorem Sierksma.public_count_eq :
    ∀ (p : Fin 9 → EuclideanSpace ℝ (Fin 3)), Nat.card {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
      Q.parts.card = 3 ∧ (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty} =
    TverbergCount 3 (fun i => EuclideanSpace.equiv (Fin 3) ℝ (p i)) :=
  @proof_Sierksma_public_count_eq
