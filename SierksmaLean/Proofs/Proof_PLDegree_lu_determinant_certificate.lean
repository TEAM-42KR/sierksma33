import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem proof_PLDegree_lu_determinant_certificate {n : ℕ}
 (M L U : Matrix (Fin n) (Fin n) ℚ) (p : Equiv.Perm (Fin n)) (d : ℚ)
 (hM : M.submatrix p id = L*U) (hL : L.IsLowerTriangular)
 (hU : U.IsUpperTriangular)
 (hd : (p.sign : ℚ) * (∏ i, L i i) * (∏ i, U i i)=d) : M.det=d := by
  have he := congrArg Matrix.det hM
  rw [Matrix.det_permute, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular L hL, Matrix.det_of_isUpperTriangular hU] at he
  have hh := congrArg (fun q : ℚ => (p.sign : ℚ)*q) he
  have hp : (p.sign : ℚ)*(p.sign : ℚ)=1 := by
    norm_cast
    simp [Int.units_mul_self]
  rw [← mul_assoc, hp, one_mul] at hh
  rw [← hd]
  exact hh.trans (mul_assoc _ _ _).symm
