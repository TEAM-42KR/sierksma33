import SierksmaLean.Proofs.Proof_Sierksma_test_map_perturbation_stability
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.test_map_perturbation_stability :
    ∀ (P : Config 9 3)
    (hP : P ∈ GenericLocus) (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi)
    (c : Fin 4 → ZMod 3), (∀ eps : ℝ, 0<eps → ∃ x : EngineParams, EngineGeneric x ∧
      CloseParams x (TestParams P pi c) eps ∧
      ∀ s ∈ (EngineCone 0).support,
        simplexDegree (EngineMap x) s=simplexDegree (EngineMap (TestParams P pi c)) s) ∧
    ConeCount (TestParams P pi c) 0 % 3=1 :=
  @proof_Sierksma_test_map_perturbation_stability
