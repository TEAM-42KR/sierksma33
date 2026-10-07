import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_test_map_degree_stability
import SierksmaLean.Theorems.Thm_Sierksma_dense_close_params
import SierksmaLean.Theorems.Thm_Sierksma_pl_equivariant_gp_dense
import SierksmaLean.Theorems.Thm_Sierksma_pl_dold_signed_count
set_option autoImplicit false
open Common PLDegree Sierksma

theorem proof_Sierksma_test_map_perturbation_stability (P : Config 9 3) (hP : P ∈ GenericLocus)
    (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3) :
    (∀ eps : ℝ, 0<eps → ∃ x : EngineParams, EngineGeneric x ∧
      CloseParams x (TestParams P pi c) eps ∧
      ∀ s ∈ (EngineCone 0).support,
        simplexDegree (EngineMap x) s=simplexDegree (EngineMap (TestParams P pi c)) s) ∧
    ConeCount (TestParams P pi c) 0 % 3=1 := by
  obtain ⟨delta,hdelta,hstable⟩ := Sierksma.test_map_degree_stability P hP pi hpi c
  have happrox : ∀ eps : ℝ, 0<eps → ∃ x : EngineParams, EngineGeneric x ∧
      CloseParams x (TestParams P pi c) eps ∧
      ∀ s ∈ (EngineCone 0).support,
        simplexDegree (EngineMap x) s=simplexDegree (EngineMap (TestParams P pi c)) s := by
    intro eps heps
    obtain ⟨x,hx,hclose⟩ := Sierksma.dense_close_params _
      Sierksma.pl_equivariant_gp_dense.1 (TestParams P pi c) (min eps delta) (lt_min heps hdelta)
    have he : CloseParams x (TestParams P pi c) eps := fun i j =>
      lt_of_lt_of_le (hclose i j) (min_le_left _ _)
    have hd : CloseParams x (TestParams P pi c) delta := fun i j =>
      lt_of_lt_of_le (hclose i j) (min_le_right _ _)
    exact ⟨x,hx,he,hstable x hd⟩
  refine ⟨happrox,?_⟩
  obtain ⟨x,hx,hclose,hdegrees⟩ := happrox 1 (by norm_num)
  have hc : ConeCount x 0=ConeCount (TestParams P pi c) 0 := by
    unfold ConeCount signedCount evaluate
    apply Finsupp.sum_congr
    intro s hs
    rw [hdegrees s hs]
  rw [← hc]
  exact (Sierksma.pl_dold_signed_count.1 x hx).2 0
