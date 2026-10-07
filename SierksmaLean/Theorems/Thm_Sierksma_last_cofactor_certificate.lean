import SierksmaLean.Proofs.Proof_Sierksma_last_cofactor_certificate
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.last_cofactor_certificate :
    ∀ (M B : Matrix (Fin 9) (Fin 9) ℚ) (d : ℚ) (hd : d ≠ 0) (hMB : M * B = d • (1 : Matrix (Fin 9) (Fin 9) ℚ)) (hB : ∀ i, B 8 i ≠ 0), M.det ≠ 0 ∧ ∀ i, LastCofactorQ M i ≠ 0 :=
  @proof_Sierksma_last_cofactor_certificate
