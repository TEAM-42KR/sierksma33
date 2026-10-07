import SierksmaLean.Proofs.Proof_Sierksma_last_cofactor_ratio_certificate
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_PLDegree_scaled_right_inverse_certificate
set_option autoImplicit false
open Sierksma

theorem Sierksma.last_cofactor_ratio_certificate :
    ∀ (M B : Matrix (Fin 9) (Fin 9) ℚ) (d : ℚ) (hd : d ≠ 0)
 (hMB : M*B=d • (1 : Matrix (Fin 9) (Fin 9) ℚ)), M.det ≠ 0 ∧ ∀ i : Fin 9, LastCofactorQ M i / M.det=B 8 i / d :=
  @proof_Sierksma_last_cofactor_ratio_certificate
