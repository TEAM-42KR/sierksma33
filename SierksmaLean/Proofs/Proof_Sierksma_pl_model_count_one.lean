import SierksmaLean.Theorems.Thm_Sierksma_model_exact_check
import SierksmaLean.Theorems.Thm_Sierksma_model_exact_geometric_bridge
set_option autoImplicit false
open Sierksma

theorem proof_Sierksma_pl_model_count_one : ModelExactCheck ∧ EngineGeneric ModelParams ∧
    ∀ j : Fin 3, ConeCount ModelParams j = 1 := by
  exact ⟨Sierksma.model_exact_check,Sierksma.model_exact_geometric_bridge Sierksma.model_exact_check⟩
