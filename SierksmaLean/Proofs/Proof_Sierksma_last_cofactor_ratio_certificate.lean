import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_PLDegree_scaled_right_inverse_certificate
set_option autoImplicit false
open Sierksma

theorem proof_Sierksma_last_cofactor_ratio_certificate
 (M B : Matrix (Fin 9) (Fin 9) ℚ) (d : ℚ) (hd : d ≠ 0)
 (hMB : M*B=d • (1 : Matrix (Fin 9) (Fin 9) ℚ)) :
 M.det ≠ 0 ∧ ∀ i : Fin 9, LastCofactorQ M i / M.det=B 8 i / d := by
  obtain ⟨hm,he⟩ := PLDegree.scaled_right_inverse_certificate M B d hd hMB
  refine ⟨hm,?_⟩
  intro i
  have hh : M.det * B 8 i = d * M.adjugate 8 i := congrArg (fun A => A 8 i) he
  have hc : M.adjugate 8 i=LastCofactorQ M i := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    change (-1 : ℚ)^(i.val+8) *
      Matrix.det (M.submatrix i.succAbove (Fin.last 8).succAbove) = _
    simp only [Fin.succAbove_last]
    rfl
  rw [hc] at hh
  apply (div_eq_div_iff hm hd).mpr
  linarith
