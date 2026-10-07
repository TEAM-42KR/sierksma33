import SierksmaLean.Theorems.Thm_PLDegree_scaled_right_inverse_certificate
set_option autoImplicit false
open scoped BigOperators
theorem proof_PLDegree_cofactor_nonzero_of_scaled_right_inverse {n : ℕ} {K : Type*} [Field K] (A B : Matrix (Fin (n+1)) (Fin (n+1)) K) (d : K) (hd : d ≠ 0) (hAB : A * B = d • (1 : Matrix (Fin (n+1)) (Fin (n+1)) K)) (i j : Fin (n+1)) (hB : B j i ≠ 0) : (-1 : K) ^ (i.val+j.val) * Matrix.det (A.submatrix i.succAbove j.succAbove) ≠ 0 := by
  obtain ⟨ha, he⟩ := PLDegree.scaled_right_inverse_certificate A B d hd hAB
  have hh : A.det * B j i = d * A.adjugate j i := congrArg (fun M => M j i) he
  have hn : A.adjugate j i ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hh
    exact (mul_ne_zero ha hB) hh
  simpa only [Matrix.adjugate_fin_succ_eq_det_submatrix] using hn
