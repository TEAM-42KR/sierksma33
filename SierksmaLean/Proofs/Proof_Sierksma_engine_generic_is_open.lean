import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree Sierksma
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem proof_Sierksma_engine_generic_is_open : IsOpen {x : EngineParams | EngineGeneric x} := by
  classical
  letI : DecidableEq ℕ := fun a b => Classical.propDecidable (a=b)
  have hR : Continuous R8 := by
    apply continuous_pi
    intro j
    unfold R8
    split_ifs <;> fun_prop
  have hv : ∀ v : ℕ, Continuous (fun x : EngineParams => EngineMap x v) := by
    intro v
    unfold EngineMap RPower
    split_ifs
    · exact (hR.iterate _).comp (continuous_apply _)
    · exact (hR.iterate _).comp (continuous_apply _)
    · exact continuous_const
  have haug : ∀ s : Finset ℕ, Continuous (fun x : EngineParams => augmentedDet (EngineMap x) s) := by
    intro s
    unfold augmentedDet
    split_ifs with hs
    · apply Continuous.matrix_det
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      unfold augmentedMatrix augment
      split_ifs
      · exact (continuous_apply _).comp (hv _)
      · exact continuous_const
    · exact continuous_const
  have hlin : ∀ s : Finset ℕ, Continuous (fun x : EngineParams => linearDet (EngineMap x) s) := by
    intro s
    unfold linearDet
    split_ifs with hs
    · apply Continuous.matrix_det
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (continuous_apply j).comp (hv _)
    · exact continuous_const
  have hs : ∀ s : Finset ℕ, IsOpen {x : EngineParams | SimplexGP (EngineMap x) s} := by
    intro s
    have heq : {x : EngineParams | SimplexGP (EngineMap x) s} =
        {x : EngineParams | s.card=9} ∩
        {x : EngineParams | augmentedDet (EngineMap x) s ≠ 0} ∩
        (⋂ v ∈ s, {x : EngineParams | linearDet (EngineMap x) (s.erase v) ≠ 0}) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, SimplexGP]
      constructor
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨h1,h2⟩,h3⟩
      · rintro ⟨⟨h1,h2⟩,h3⟩
        exact ⟨h1,h2,h3⟩
    rw [heq]
    apply IsOpen.inter
    · apply IsOpen.inter
      · by_cases hh : s.card=9 <;> simp [hh]
      · exact isOpen_ne.preimage (haug s)
    · apply isOpen_biInter_finset
      intro v hv
      exact isOpen_ne.preimage (hlin (s.erase v))
  have heq : {x : EngineParams | EngineGeneric x} =
      ⋂ j : Fin 3, ⋂ s ∈ (EngineCone j).support, {x : EngineParams | SimplexGP (EngineMap x) s} := by
    ext x
    simp [EngineGeneric, ChainGP]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_biInter_finset
  exact fun s _ => hs s
