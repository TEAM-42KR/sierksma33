import SierksmaLean.Definitions.Def_Common_TverbergPartitions

/-!
# Head statements

* `MainStatement` is the statement proved as `Sierksma.main`
  (definitions: `SierksmaLean/Definitions/Def_Common_TverbergPartitions.lean`).
* `PublicStatement` is the same bound in Mathlib vocabulary (also `Challenge.lean`, which imports only Mathlib).
-/

open Common

namespace SierksmaLean

/-- Every labelled 9-tuple in ℝ³ has at least 8 unordered Tverberg 3-partitions (form used by the proof). -/
def MainStatement : Prop := ∀ P : Config 9 3, 8 ≤ TverbergCount 3 P

/-- The same bound in Mathlib vocabulary (`Finpartition`, `convexHull`, `EuclideanSpace`). -/
def PublicStatement : Prop :=
  ∀ p : Fin 9 → EuclideanSpace ℝ (Fin 3),
    8 ≤ Nat.card {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
      Q.parts.card = 3 ∧
        (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty}

end SierksmaLean
