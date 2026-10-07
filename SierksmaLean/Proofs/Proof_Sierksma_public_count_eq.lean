import SierksmaLean.Definitions.Def_Common_TverbergPartitions
set_option autoImplicit false
open scoped BigOperators
open Common

theorem proof_Sierksma_public_count_eq (p : Fin 9 → EuclideanSpace ℝ (Fin 3)) :
    Nat.card {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
      Q.parts.card = 3 ∧ (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty} =
    TverbergCount 3 (fun i => EuclideanSpace.equiv (Fin 3) ℝ (p i)) := by
  classical
  set e := EuclideanSpace.equiv (Fin 3) ℝ with he
  set P : Config 9 3 := fun i => e (p i) with hP
  have hconv : ∀ A : Finset (Fin 9),
      convexHull ℝ (P '' (A : Set (Fin 9))) = e '' convexHull ℝ (p '' (A : Set (Fin 9))) := by
    intro A
    have h1 : P '' (A : Set (Fin 9)) = e '' (p '' (A : Set (Fin 9))) := by
      rw [Set.image_image]
    rw [h1]
    exact (LinearMap.image_convexHull (e.toLinearEquiv.toLinearMap) _).symm
  have hmem : ∀ (A : Finset (Fin 9)) (x : EuclideanSpace ℝ (Fin 3)),
      e x ∈ convexHull ℝ (P '' (A : Set (Fin 9))) ↔ x ∈ convexHull ℝ (p '' (A : Set (Fin 9))) := by
    intro A x
    rw [hconv A]
    exact e.injective.mem_set_image
  have hhull : ∀ Q : Finset (Finset (Fin 9)),
      (⋂ A ∈ Q, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty ↔ HasCommonHull P Q := by
    intro Q
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨e x, fun A hA => (hmem A x).2 (Set.mem_iInter₂.1 hx A hA)⟩
    · rintro ⟨z, hz⟩
      refine ⟨e.symm z, Set.mem_iInter₂.2 fun A hA => (hmem A (e.symm z)).1 ?_⟩
      rw [e.apply_symm_apply]
      exact hz A hA
  have hblocks : ∀ Q : Finpartition (Finset.univ : Finset (Fin 9)),
      BlocksOn Q.parts Finset.univ := by
    intro Q
    refine ⟨fun A hA => ⟨Q.nonempty_of_mem_parts hA, Finset.subset_univ A⟩, ?_, Q.biUnion_parts⟩
    intro A hA B hB hAB
    exact Q.disjoint hA hB hAB
  have hmemT : ∀ Q : Finset (Finset (Fin 9)),
      Q ∈ TverbergPartitions 3 P ↔ (BlocksOn Q Finset.univ ∧ Q.card = 3) ∧ HasCommonHull P Q := by
    intro Q
    simp only [TverbergPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  let toFP : {Q : Finset (Finset (Fin 9)) // Q ∈ TverbergPartitions 3 P} →
      {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
        Q.parts.card = 3 ∧ (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty} :=
    fun Q =>
      have hQ := (hmemT Q.1).1 Q.2
      ⟨{ parts := Q.1
         supIndep := by
           rw [Finset.supIndep_iff_pairwiseDisjoint]
           intro A hA B hB hAB
           exact hQ.1.1.2.1 A hA B hB hAB
         sup_parts := by
           rw [Finset.sup_eq_biUnion]
           exact hQ.1.1.2.2
         bot_notMem := by
           intro h
           have := (hQ.1.1.1 ⊥ h).1
           simp at this },
        hQ.1.2, (hhull Q.1).2 hQ.2⟩
  have eqv : {Q : Finpartition (Finset.univ : Finset (Fin 9)) //
        Q.parts.card = 3 ∧ (⋂ A ∈ Q.parts, convexHull ℝ (p '' (A : Set (Fin 9)))).Nonempty} ≃
      {Q : Finset (Finset (Fin 9)) // Q ∈ TverbergPartitions 3 P} :=
    { toFun := fun Q => ⟨Q.1.parts, (hmemT _).2 ⟨⟨hblocks Q.1, Q.2.1⟩, (hhull _).1 Q.2.2⟩⟩
      invFun := toFP
      left_inv := fun Q => Subtype.ext (Finpartition.ext rfl)
      right_inv := fun Q => Subtype.ext rfl }
  rw [Nat.card_congr eqv, Nat.card_eq_finsetCard]
  rfl
