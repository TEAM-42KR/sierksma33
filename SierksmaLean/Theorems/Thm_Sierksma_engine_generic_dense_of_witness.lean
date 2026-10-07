import SierksmaLean.Proofs.Proof_Sierksma_engine_generic_dense_of_witness
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree Sierksma

theorem Sierksma.engine_generic_dense_of_witness :
    ∀ (w : EngineParams) (hw : EngineGeneric w), Dense {x : EngineParams | EngineGeneric x} :=
  @proof_Sierksma_engine_generic_dense_of_witness
