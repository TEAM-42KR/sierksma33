import SierksmaLean.Proofs.Proof_PLDegree_polynomial_nonzero_open_dense
import Mathlib
set_option autoImplicit false

theorem PLDegree.polynomial_nonzero_open_dense :
    ∀ {k : ℕ}
    (p : MvPolynomial (Fin k) ℝ) (hp : p ≠ 0), IsOpen {x : Fin k → ℝ | MvPolynomial.eval x p ≠ 0} ∧
    Dense {x : Fin k → ℝ | MvPolynomial.eval x p ≠ 0} :=
  @proof_PLDegree_polynomial_nonzero_open_dense
