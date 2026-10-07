import Mathlib

/-!
# Sierksma's conjecture for d = 3, r = 3 (challenge statement)

The statement uses Mathlib vocabulary only. `Solution.lean` proves the same declaration;
`config.json` lets Comparator check that with the standard axioms only.
-/

theorem sierksma_three_three (p : Fin 9 → EuclideanSpace ℝ (Fin 3)) :
    8 ≤ Nat.card {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
      Q.parts.card = 3 ∧
        (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty} := by
  sorry
