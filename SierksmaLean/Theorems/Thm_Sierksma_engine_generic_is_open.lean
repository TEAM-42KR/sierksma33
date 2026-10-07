import SierksmaLean.Proofs.Proof_Sierksma_engine_generic_is_open
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree Sierksma

theorem Sierksma.engine_generic_is_open :
    IsOpen {x : EngineParams | EngineGeneric x} :=
  @proof_Sierksma_engine_generic_is_open
