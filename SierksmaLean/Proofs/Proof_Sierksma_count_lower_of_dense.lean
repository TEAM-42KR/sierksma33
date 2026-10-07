import SierksmaLean.Definitions.Def_Common_TverbergPartitions
set_option autoImplicit false
open scoped BigOperators
open Common

theorem proof_Sierksma_count_lower_of_dense (D : Set (Config 9 3)) (hD : Dense D) (k : ℕ)
    (hk : ∀ P ∈ D, k ≤ TverbergCount 3 P) (P : Config 9 3) : k ≤ TverbergCount 3 P := by
  classical
  have partitionClosed (Q : Common.Partition 9) :
      IsClosed {P : Common.Config 9 3 | Common.IsTverberg 3 P Q} := by
    classical
    have hullSimplex (n d : ℕ) (P : Common.Config n d)
        (A : Common.Block n) (z : Fin d → ℝ) :
        z ∈ convexHull ℝ (P '' (↑A : Set (Fin n))) ↔
          ∃ w : stdSimplex ℝ A, (∑ v : A, (w.val v) • P v.val) = z := by
      classical
      let L : (A → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
        ∑ v : A, (LinearMap.proj (R := ℝ) v).smulRight (P v.val)
      have hL (w : A → ℝ) : L w = ∑ v : A, w v • P v.val := by
        simp [L, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
      have hbase : L '' Set.range (fun i j : A => if i = j then (1 : ℝ) else 0) =
          P '' (↑A : Set (Fin n)) := by
        have hb (i : A) : L (fun j : A => if i = j then (1 : ℝ) else 0) = P i.val := by
          rw [hL]
          simp [eq_comm]
        rw [← Set.range_comp']
        simp_rw [hb]
        exact (Set.image_eq_range P (↑A : Set (Fin n))).symm
      have himg : L '' stdSimplex ℝ A = convexHull ℝ (P '' (↑A : Set (Fin n))) := by
        rw [← convexHull_basis_eq_stdSimplex, L.image_convexHull, hbase]
      rw [← himg]
      constructor
      · rintro ⟨w, hw, h⟩
        exact ⟨⟨w, hw⟩, (hL w).symm.trans h⟩
      · rintro ⟨w, h⟩
        exact ⟨w.val, w.property, (hL w.val).trans h⟩
    by_cases hQ : IsPartition Q 3
    · have hne : Q.Nonempty := Finset.card_pos.mp (by rw [hQ.2]; omega)
      obtain ⟨A0, hA0⟩ := hne
      let J := {A : Block 9 // A ∈ Q}
      let K := (A : J) → stdSimplex ℝ A.val
      let a0 : J := ⟨A0, hA0⟩
      let b : Config 9 3 → K → J → (Fin 3 → ℝ) :=
        fun P w A => ∑ v : A.val, (w A).val v • P v.val
      let C : Set (Config 9 3 × K) :=
        {t | ∀ A : J, b t.1 t.2 A = b t.1 t.2 a0}
      have hb (A : J) : Continuous (fun t : Config 9 3 × K => b t.1 t.2 A) := by
        dsimp only [b]
        apply continuous_finset_sum
        intro v hv
        have hc : Continuous (fun t : Config 9 3 × K => t.2 A) :=
          (show Continuous (fun w : K => w A) from continuous_apply A).comp continuous_snd
        have hvcoef : Continuous (fun t : Config 9 3 × K => (t.2 A).val v) :=
          (continuous_apply v).comp
            ((show Continuous (fun w : stdSimplex ℝ A.val => w.val) from
              continuous_subtype_val).comp hc)
        exact hvcoef.smul ((continuous_apply v.val).comp continuous_fst)
      have hC : IsClosed C := by
        simp only [C, Set.setOf_forall]
        exact isClosed_iInter (fun A => isClosed_eq (hb A) (hb a0))
      have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
      have hset : {P : Config 9 3 | IsTverberg 3 P Q} = Prod.fst '' C := by
        ext P
        constructor
        · intro h
          obtain ⟨z, hz⟩ := h.2
          have hcoeff : ∀ A : J, ∃ w : stdSimplex ℝ A.val,
              (∑ v : A.val, w.val v • P v.val) = z := by
            intro A
            exact (hullSimplex 9 3 P A.val z).mp (hz A.val A.property)
          choose w hw using hcoeff
          refine ⟨(P, w), ?_, rfl⟩
          intro A
          exact (hw A).trans (hw a0).symm
        · rintro ⟨⟨P', w⟩, hw, rfl⟩
          refine ⟨hQ, b P' w a0, ?_⟩
          intro A hA
          apply (hullSimplex 9 3 P' A (b P' w a0)).mpr
          exact ⟨w ⟨A, hA⟩, hw ⟨A, hA⟩⟩
      rw [hset]
      exact hproj
    · have hset : {P : Config 9 3 | IsTverberg 3 P Q} = ∅ := by
        ext P
        simp [IsTverberg, hQ]
      rw [hset]
      exact isClosed_empty
  let U : Set (Config 9 3) :=
    {P' | ∀ Q : Common.Partition 9, ¬ IsTverberg 3 P Q → ¬ IsTverberg 3 P' Q}
  have ho : IsOpen U := by
    simp only [U, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro Q
    by_cases hQ : IsTverberg 3 P Q
    · simpa [hQ] using (isOpen_univ : IsOpen (Set.univ : Set (Config 9 3)))
    · simp only [hQ, not_false_eq_true, Set.iInter_true]
      exact (partitionClosed Q).isOpen_compl
  have hPU : P ∈ U := fun Q hQ => hQ
  obtain ⟨P', hP'D, hP'U⟩ := hD.exists_mem_open ho ⟨P, hPU⟩
  have hsub : TverbergPartitions 3 P' ⊆ TverbergPartitions 3 P := by
    intro Q hQ
    simp only [TverbergPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at hQ ⊢
    by_contra hn
    exact hP'U Q hn hQ
  exact (hk P' hP'D).trans (Finset.card_le_card hsub)
