import SierksmaLean.Main

theorem sierksma_three_three (p : Fin 9 → EuclideanSpace ℝ (Fin 3)) :
    8 ≤ Nat.card {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
      Q.parts.card = 3 ∧
        (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty} :=
  SierksmaLean.sierksma_three_three p
