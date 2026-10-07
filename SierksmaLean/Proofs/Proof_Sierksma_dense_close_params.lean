import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma

theorem proof_Sierksma_dense_close_params (S : Set EngineParams) (hS : Dense S) (x : EngineParams)
    (eps : ℝ) (heps : 0<eps) : ∃ y ∈ S, CloseParams y x eps := by
  have hopen : IsOpen {y : EngineParams | CloseParams y x eps} := by
    simp only [CloseParams,Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    have hc : Continuous (fun y : EngineParams => y i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact isOpen_lt (hc.sub continuous_const).abs continuous_const
  have hself : x ∈ {y : EngineParams | CloseParams y x eps} := by
    intro i j
    simpa using heps
  exact hS.exists_mem_open hopen ⟨x,hself⟩
