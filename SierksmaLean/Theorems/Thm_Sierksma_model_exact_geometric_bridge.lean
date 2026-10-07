import SierksmaLean.Proofs.Proof_Sierksma_model_exact_geometric_bridge
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree Sierksma
open scoped BigOperators

theorem Sierksma.model_exact_geometric_bridge :
    ∀ (h : ModelExactCheck), EngineGeneric ModelParams ∧ ∀ j : Fin 3, ConeCount ModelParams j = 1 :=
  @proof_Sierksma_model_exact_geometric_bridge
