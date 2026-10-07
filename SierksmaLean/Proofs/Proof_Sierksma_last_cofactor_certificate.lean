import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_PLDegree_scaled_right_inverse_certificate
import SierksmaLean.Theorems.Thm_PLDegree_cofactor_nonzero_of_scaled_right_inverse
set_option autoImplicit false
open Sierksma
theorem proof_Sierksma_last_cofactor_certificate (M B : Matrix (Fin 9) (Fin 9) ℚ) (d : ℚ) (hd : d ≠ 0) (hMB : M * B = d • (1 : Matrix (Fin 9) (Fin 9) ℚ)) (hB : ∀ i, B 8 i ≠ 0) : M.det ≠ 0 ∧ ∀ i, LastCofactorQ M i ≠ 0 := by
  refine ⟨(PLDegree.scaled_right_inverse_certificate M B d hd hMB).1, ?_⟩
  intro i
  have hi := PLDegree.cofactor_nonzero_of_scaled_right_inverse M B d hd hMB i (Fin.last 8) (hB i)
  simp only [Fin.val_last, Fin.succAbove_last] at hi
  exact hi
