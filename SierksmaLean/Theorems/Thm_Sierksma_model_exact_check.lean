import SierksmaLean.Proofs.Proof_Sierksma_model_exact_check
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem Sierksma.model_exact_check :
    ModelExactCheck :=
  @proof_Sierksma_model_exact_check
