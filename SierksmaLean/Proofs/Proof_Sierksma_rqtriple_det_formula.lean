import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
theorem proof_Sierksma_rqtriple_det_formula (P : RQConfig) (s : Fin 3 → Fin 9) (q : Fin 3 → ℚ) : RQTripleDet P s q =
    (P (s 1) 0-P (s 0) 0)*(P (s 2) 1-P (s 0) 1)*q 2 -
    (P (s 1) 0-P (s 0) 0)*(P (s 2) 2-P (s 0) 2)*q 1 -
    (P (s 1) 1-P (s 0) 1)*(P (s 2) 0-P (s 0) 0)*q 2 +
    (P (s 1) 1-P (s 0) 1)*(P (s 2) 2-P (s 0) 2)*q 0 +
    (P (s 1) 2-P (s 0) 2)*(P (s 2) 0-P (s 0) 0)*q 1 -
    (P (s 1) 2-P (s 0) 2)*(P (s 2) 1-P (s 0) 1)*q 0 := by
  change Matrix.det (Matrix.of ![P (s 1)-P (s 0), P (s 2)-P (s 0), q]) = _
  rw [Matrix.det_fin_three]
  simp [Matrix.of_apply, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
