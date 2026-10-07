import SierksmaLean.Theorems.Thm_Sierksma_public_count_eq
set_option autoImplicit false
open scoped BigOperators
open Common

theorem proof_Sierksma_public_iff :
    (∀ p : Fin 9 → EuclideanSpace ℝ (Fin 3),
      8 ≤ Nat.card {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
        Q.parts.card = 3 ∧
          (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty}) ↔
    ∀ P : Config 9 3, 8 ≤ TverbergCount 3 P := by
  constructor
  · intro h P
    have h' := h (fun i => (EuclideanSpace.equiv (Fin 3) ℝ).symm (P i))
    rw [Sierksma.public_count_eq] at h'
    have hP : (fun i => (EuclideanSpace.equiv (Fin 3) ℝ)
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm (P i))) = P :=
      funext fun i => (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply (P i)
    rw [hP] at h'
    exact h'
  · intro h p
    rw [Sierksma.public_count_eq]
    exact h _
