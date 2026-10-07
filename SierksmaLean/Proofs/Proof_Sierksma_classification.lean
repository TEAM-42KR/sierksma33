import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_Amplification
import SierksmaLean.Definitions.Def_Sierksma_FractionalCover
import SierksmaLean.Definitions.Def_Sierksma_TwistedRealization
set_option autoImplicit false
open Common Sierksma
open scoped BigOperators
set_option maxRecDepth 4000
theorem proof_Sierksma_classification (P : Config 9 3) (hP : StrongGP P) (Q : Common.Partition 9) (hQ : BlocksOn Q (Q.biUnion id)) (hcard : Q.card = 3) (hz : HasCommonHull P Q) : Q ∈ Universe 3 := by
  classical
  have hsupport (A : Block 9) (z : Fin 3 → ℝ) (hz : z ∈ convexHull ℝ (P '' (↑A : Set (Fin 9)))) : ∃ B : Block 9, B ⊆ A ∧ B.Nonempty ∧ B.card ≤ 4 ∧ z ∈ convexHull ℝ (P '' (↑B : Set (Fin 9))) := by
    rw [convexHull_eq_union] at hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨t, htA, htind, hzt⟩ := hz
    have hc : t.card ≤ 4 := by
      have h := htind.card_le_finrank_succ
      have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → (Fin 3 → ℝ))))
      have hdim3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
      simp only [Fintype.card_coe] at h
      omega
    have hx : ∀ x : t, ∃ i : Fin 9, i ∈ A ∧ P i = x := fun x => htA x.property
    choose g hgA hg using hx
    let B : Block 9 := Finset.univ.image g
    have himage : P '' (↑B : Set (Fin 9)) = (↑t : Set (Fin 3 → ℝ)) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hi
        rw [hg y]
        exact y.property
      · intro hx
        refine ⟨g ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩, hg ⟨x, hx⟩⟩
    have hzB : z ∈ convexHull ℝ (P '' (↑B : Set (Fin 9))) := by rwa [himage]
    refine ⟨B, ?_, ?_, ?_, hzB⟩
    · intro i hi
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hi
      exact hgA y
    · by_contra hn
      have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [he] at hzB
    · exact (Finset.card_image_le).trans (by simpa using hc)
  have hpair (A B : Block 9) (hd : Disjoint A B) (z : Fin 3 → ℝ)
      (ha : z ∈ convexHull ℝ (P '' (↑A : Set (Fin 9))))
      (hb : z ∈ convexHull ℝ (P '' (↑B : Set (Fin 9)))) : 5 ≤ A.card + B.card := by
    by_contra hn
    have hind := hP.1 (A ∪ B) (by rw [Finset.card_union_of_disjoint hd]; omega)
    let p : {i // i ∈ A ∪ B} → (Fin 3 → ℝ) := fun i => P i.val
    let s : Set {i // i ∈ A ∪ B} := {i | i.val ∈ A}
    let t : Set {i // i ∈ A ∪ B} := {i | i.val ∈ B}
    have hs : p '' s = P '' (↑A : Set (Fin 9)) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.val, hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, Finset.mem_union_left _ hi⟩, hi, rfl⟩
    have ht : p '' t = P '' (↑B : Set (Fin 9)) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.val, hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, Finset.mem_union_right _ hi⟩, hi, rfl⟩
    have ha' : z ∈ affineSpan ℝ (p '' s) := by
      rw [hs]
      exact convexHull_subset_affineSpan _ ha
    have hb' : z ∈ affineSpan ℝ (p '' t) := by
      rw [ht]
      exact convexHull_subset_affineSpan _ hb
    obtain ⟨i, hi, hj⟩ := hind.exists_mem_inter_of_exists_mem_inter_affineSpan ha' hb'
    exact Finset.disjoint_left.mp hd hi hj
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ ({a,b,c} : Common.Partition 9) := by simp
  have hb : b ∈ ({a,b,c} : Common.Partition 9) := by simp
  have hc : c ∈ ({a,b,c} : Common.Partition 9) := by simp
  have dab := hQ.2.1 a ha b hb hab
  have dac := hQ.2.1 a ha c hc hac
  have dbc := hQ.2.1 b hb c hc hbc
  obtain ⟨z,hz⟩ := hz
  obtain ⟨A,hAa,hAne,hA4,hzA⟩ := hsupport a z (hz a ha)
  obtain ⟨B,hBb,hBne,hB4,hzB⟩ := hsupport b z (hz b hb)
  obtain ⟨C,hCc,hCne,hC4,hzC⟩ := hsupport c z (hz c hc)
  have dAB : Disjoint A B := dab.mono hAa hBb
  have dAC : Disjoint A C := dac.mono hAa hCc
  have dBC : Disjoint B C := dbc.mono hBb hCc
  have hAB := hpair A B dAB z hzA hzB
  have hAC := hpair A C dAC z hzA hzC
  have hBC := hpair B C dBC z hzB hzC
  have hAz := convexHull_subset_affineSpan _ hzA
  have hBz := convexHull_subset_affineSpan _ hzB
  have hCz := convexHull_subset_affineSpan _ hzC
  have noA : ¬ (A.card = 2 ∧ B.card = 3 ∧ C.card = 3) := by
    rintro ⟨hA,hB,hC⟩
    exact hP.2 A B C hA hB hC dAB dAC dBC ⟨z,hAz,hBz,hCz⟩
  have noB : ¬ (B.card = 2 ∧ A.card = 3 ∧ C.card = 3) := by
    rintro ⟨hB,hA,hC⟩
    exact hP.2 B A C hB hA hC dAB.symm dBC dAC ⟨z,hBz,hAz,hCz⟩
  have noC : ¬ (C.card = 2 ∧ A.card = 3 ∧ B.card = 3) := by
    rintro ⟨hC,hA,hB⟩
    exact hP.2 C A B hC hA hB dAC.symm dBC.symm dAB ⟨z,hCz,hAz,hBz⟩
  have hA1 := Finset.card_pos.mpr hAne
  have hB1 := Finset.card_pos.mpr hBne
  have hC1 := Finset.card_pos.mpr hCne
  have hsum : 9 ≤ A.card + B.card + C.card := by omega
  have hUnionCard : (a ∪ b ∪ c).card = a.card + b.card + c.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dac,dbc⟩), Finset.card_union_of_disjoint dab]
  have hOrig : a.card + b.card + c.card ≤ 9 := by
    simpa only [hUnionCard, Fintype.card_fin] using Finset.card_le_univ (a ∪ b ∪ c)
  have hAaC := Finset.card_le_card hAa
  have hBbC := Finset.card_le_card hBb
  have hCcC := Finset.card_le_card hCc
  have ha4 : a.card ≤ 4 := by omega
  have hb4 : b.card ≤ 4 := by omega
  have hc4 : c.card ≤ 4 := by omega
  have hfull : ({a,b,c} : Common.Partition 9).biUnion id = Finset.univ := by
    have hh : a ∪ b ∪ c = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    simpa [Finset.biUnion_insert, Finset.union_assoc] using hh
  simp only [Universe, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨?_, hcard⟩, ?_⟩
  · rw [← hfull]
    exact hQ
  · intro D hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl
    · exact ha4
    · exact hb4
    · exact hc4
