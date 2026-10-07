import SierksmaLean.Proofs.Proof_Sierksma_test_map_degree_stability
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common PLDegree Sierksma

theorem Sierksma.test_map_degree_stability :
    ∀ (P : Config 9 3) (hP : P ∈ GenericLocus) (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3), ∃ delta : ℝ, 0<delta ∧ ∀ x : EngineParams, CloseParams x (TestParams P pi c) delta → ∀ s ∈ (EngineCone 0).support, PLDegree.simplexDegree (EngineMap x) s=PLDegree.simplexDegree (EngineMap (TestParams P pi c)) s :=
  @proof_Sierksma_test_map_degree_stability
