import SierksmaLean.Proofs.Proof_PLDegree_finite_hull_zero_closed
import SierksmaLean.Definitions.Def_PLDegree_Chain
set_option autoImplicit false
open PLDegree

theorem PLDegree.finite_hull_zero_closed :
    ∀ {V : Type*} [LinearOrder V] {n : ℕ} (s : Finset V), IsClosed {F : V → Fin n → ℝ | (0 : Fin n → ℝ) ∈ hull F s} :=
  @proof_PLDegree_finite_hull_zero_closed
