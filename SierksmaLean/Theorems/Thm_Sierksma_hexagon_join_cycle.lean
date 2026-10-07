import SierksmaLean.Proofs.Proof_Sierksma_hexagon_join_cycle
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.hexagon_join_cycle :
    Homogeneous 8 HexCycle ∧ IsCycle HexCycle ∧
    relabel ShiftVertex HexCycle=HexCycle ∧
    (∀ s ∈ HexCycle.support, ∀ v ∈ s, v<24 ∧ ShiftVertex v ∉ s ∧
      ShiftVertex (ShiftVertex v) ∉ s) :=
  @proof_Sierksma_hexagon_join_cycle
