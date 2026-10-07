import SierksmaLean.Proofs.Proof_PLDegree_cofactor_nonzero_of_scaled_right_inverse
import Mathlib
set_option autoImplicit false

theorem PLDegree.cofactor_nonzero_of_scaled_right_inverse :
    ∀ {n : ℕ} {K : Type*} [Field K] (A B : Matrix (Fin (n+1)) (Fin (n+1)) K) (d : K) (hd : d ≠ 0) (hAB : A * B = d • (1 : Matrix (Fin (n+1)) (Fin (n+1)) K)) (i j : Fin (n+1)) (hB : B j i ≠ 0), (-1 : K) ^ (i.val+j.val) * Matrix.det (A.submatrix i.succAbove j.succAbove) ≠ 0 :=
  @proof_PLDegree_cofactor_nonzero_of_scaled_right_inverse
