import SierksmaLean.Proofs.Proof_Sierksma_pl_dold_signed_count
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.pl_dold_signed_count :
    (∀ x : EngineParams, EngineGeneric x →
      (∀ j k : Fin 3, ConeCount x j=ConeCount x k) ∧
      ∀ j : Fin 3, ConeCount x j % 3=1) ∧
    (∀ x : EngineParams, ∃ j : Fin 3, ∃ s ∈ (EngineCone j).support,
      (0 : W8) ∈ PLDegree.hull (EngineMap x) s) :=
  @proof_Sierksma_pl_dold_signed_count
