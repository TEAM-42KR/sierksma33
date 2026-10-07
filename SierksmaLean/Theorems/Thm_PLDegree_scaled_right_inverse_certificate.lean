import SierksmaLean.Proofs.Proof_PLDegree_scaled_right_inverse_certificate
import Mathlib
set_option autoImplicit false

theorem PLDegree.scaled_right_inverse_certificate :
    ∀ {n : ℕ} {K : Type*} [Field K] (A B : Matrix (Fin n) (Fin n) K) (d : K) (hd : d ≠ 0) (hAB : A * B = d • (1 : Matrix (Fin n) (Fin n) K)), A.det ≠ 0 ∧ A.det • B = d • A.adjugate :=
  @proof_PLDegree_scaled_right_inverse_certificate
