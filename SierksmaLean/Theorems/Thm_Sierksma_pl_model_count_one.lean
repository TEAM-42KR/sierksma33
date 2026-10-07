import SierksmaLean.Proofs.Proof_Sierksma_pl_model_count_one
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.pl_model_count_one :
    ModelExactCheck ∧ EngineGeneric ModelParams ∧
      ∀ j : Fin 3, ConeCount ModelParams j=1 :=
  @proof_Sierksma_pl_model_count_one
