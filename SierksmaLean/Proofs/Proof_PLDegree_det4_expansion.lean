import Mathlib
set_option autoImplicit false
open scoped BigOperators
theorem proof_PLDegree_det4_expansion (M : Matrix (Fin 4) (Fin 4) ℚ) :
    M.det = M 0 0 * M 1 1 * M 2 2 * M 3 3
      - M 0 0 * M 1 1 * M 2 3 * M 3 2
      - M 0 0 * M 1 2 * M 2 1 * M 3 3
      + M 0 0 * M 1 2 * M 2 3 * M 3 1
      + M 0 0 * M 1 3 * M 2 1 * M 3 2
      - M 0 0 * M 1 3 * M 2 2 * M 3 1
      - M 0 1 * M 1 0 * M 2 2 * M 3 3
      + M 0 1 * M 1 0 * M 2 3 * M 3 2
      + M 0 1 * M 1 2 * M 2 0 * M 3 3
      - M 0 1 * M 1 2 * M 2 3 * M 3 0
      - M 0 1 * M 1 3 * M 2 0 * M 3 2
      + M 0 1 * M 1 3 * M 2 2 * M 3 0
      + M 0 2 * M 1 0 * M 2 1 * M 3 3
      - M 0 2 * M 1 0 * M 2 3 * M 3 1
      - M 0 2 * M 1 1 * M 2 0 * M 3 3
      + M 0 2 * M 1 1 * M 2 3 * M 3 0
      + M 0 2 * M 1 3 * M 2 0 * M 3 1
      - M 0 2 * M 1 3 * M 2 1 * M 3 0
      - M 0 3 * M 1 0 * M 2 1 * M 3 2
      + M 0 3 * M 1 0 * M 2 2 * M 3 1
      + M 0 3 * M 1 1 * M 2 0 * M 3 2
      - M 0 3 * M 1 1 * M 2 2 * M 3 0
      - M 0 3 * M 1 2 * M 2 0 * M 3 1
      + M 0 3 * M 1 2 * M 2 1 * M 3 0  := by
  have hf : (Fin.succAbove : Fin 4 → Fin 3 → Fin 4) =
      ![![1,2,3], ![0,2,3], ![0,1,3], ![0,1,2]] := by decide +kernel
  have hs : (Fin.succ : Fin 3 → Fin 4) = ![1,2,3] := by decide +kernel
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [hf, hs, Matrix.vecHead, Matrix.vecTail, Fin.succ]
  ring
