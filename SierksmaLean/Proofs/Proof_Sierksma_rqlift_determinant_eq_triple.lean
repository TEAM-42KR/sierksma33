import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_PLDegree_det4_expansion
set_option autoImplicit false
open Sierksma

theorem proof_Sierksma_rqlift_determinant_eq_triple (P : RQConfig) (u : Fin 9) (t : Fin 3 → Fin 9) :
    Matrix.det (Matrix.of (fun i j : Fin 4 => RQLift P (![u,t 0,t 1,t 2] i) j.val)) =
      RQTripleDet P t (P u-P (t 0)) := by
  have h3 (q : Fin 3 → ℚ) : RQTripleDet P t q =
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 1-P (t 0) 1)*q 2 -
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 2-P (t 0) 2)*q 1 -
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 0-P (t 0) 0)*q 2 +
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 2-P (t 0) 2)*q 0 +
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 0-P (t 0) 0)*q 1 -
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 1-P (t 0) 1)*q 0 := by
    change Matrix.det (Matrix.of ![P (t 1)-P (t 0), P (t 2)-P (t 0), q]) = _
    rw [Matrix.det_fin_three]
    simp [Matrix.of_apply, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
  rw [PLDegree.det4_expansion, h3]
  norm_num [RQLift, Matrix.of_apply, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
  have hv2 : (![u,t 0,t 1,t 2] : Fin 4 → Fin 9) 2 = t 1 := rfl
  have hv3 : (![u,t 0,t 1,t 2] : Fin 4 → Fin 9) 3 = t 2 := rfl
  have hc2 (h : 2 < 3) : (⟨2,h⟩ : Fin 3) = 2 := rfl
  simp only [hv2, hv3, hc2]
  ring
