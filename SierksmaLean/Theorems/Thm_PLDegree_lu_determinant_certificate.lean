import SierksmaLean.Proofs.Proof_PLDegree_lu_determinant_certificate
import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem PLDegree.lu_determinant_certificate :
    ∀ {n : ℕ}
 (M L U : Matrix (Fin n) (Fin n) ℚ) (p : Equiv.Perm (Fin n)) (d : ℚ)
 (hM : M.submatrix p id = L*U) (hL : L.IsLowerTriangular)
 (hU : U.IsUpperTriangular)
 (hd : (p.sign : ℚ) * (∏ i, L i i) * (∏ i, U i i)=d), M.det=d :=
  @proof_PLDegree_lu_determinant_certificate
