import SierksmaLean.Proofs.Proof_Sierksma_engine_generic_prefix_auxiliary
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree Sierksma

theorem Sierksma.engine_generic_prefix_auxiliary :
    ∀ (x y : EngineParams)
    (hx : EngineGeneric x) (hy : EngineGeneric y), ∃ z : EngineParams, (∀ t : Fin 10,
      EngineGeneric (fun r => if r.val<t.val then z r else x r)) ∧
      (∀ t : Fin 10, EngineGeneric (fun r => if r.val<t.val then z r else y r)) :=
  @proof_Sierksma_engine_generic_prefix_auxiliary
