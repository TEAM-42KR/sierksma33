import SierksmaLean.Theorems.Thm_Sierksma_ModelFacet_all
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem proof_Sierksma_model_exact_check : ModelExactCheck := by
  refine ⟨fun a => ⟨(Sierksma.ModelFacet.all a).1,(Sierksma.ModelFacet.all a).2.1⟩,?_⟩
  unfold ModelCountQ
  calc
    _ = ∑ a : Fin 4 → Fin 6, if a=0 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Sierksma.ModelFacet.all a).2.2
    _ = 1 := by
      classical
      simp
