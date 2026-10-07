import Mathlib
set_option autoImplicit false
theorem proof_PLDegree_scaled_right_inverse_certificate {n : ℕ} {K : Type*} [Field K] (A B : Matrix (Fin n) (Fin n) K) (d : K) (hd : d ≠ 0) (hAB : A * B = d • (1 : Matrix (Fin n) (Fin n) K)) : A.det ≠ 0 ∧ A.det • B = d • A.adjugate := by
  have hdet : A.det * B.det = d^n := by
    calc
      A.det * B.det = (A * B).det := (Matrix.det_mul A B).symm
      _ = (d • (1 : Matrix (Fin n) (Fin n) K)).det := congrArg Matrix.det hAB
      _ = d ^ n := by simp [Matrix.det_smul]
  have ha : A.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hdet
    exact pow_ne_zero n hd hdet.symm
  refine ⟨ha, ?_⟩
  calc
    A.det • B = (A.adjugate * A) * B := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = A.adjugate * (A * B) := Matrix.mul_assoc _ _ _
    _ = A.adjugate * (d • (1 : Matrix (Fin n) (Fin n) K)) := by rw [hAB]
    _ = d • A.adjugate := by rw [Matrix.mul_smul, Matrix.mul_one]
