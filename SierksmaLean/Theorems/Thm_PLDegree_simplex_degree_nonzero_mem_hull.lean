import SierksmaLean.Proofs.Proof_PLDegree_simplex_degree_nonzero_mem_hull
import SierksmaLean.Definitions.Def_PLDegree_Chain
set_option autoImplicit false
open PLDegree

theorem PLDegree.simplex_degree_nonzero_mem_hull :
    ∀ {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (h : simplexDegree F s ≠ 0), (0 : Fin n → ℝ) ∈ hull F s :=
  @proof_PLDegree_simplex_degree_nonzero_mem_hull
