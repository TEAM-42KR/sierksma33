import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma Set Filter Topology
open scoped BigOperators

theorem proof_Sierksma_generic_locus_open_dense_of_nonempty (h : GenericLocus.Nonempty) : Dense GenericLocus ∧ IsOpen GenericLocus := by
  classical
  obtain ⟨w, hw⟩ := h
  have hcoord (v : Fin 9) (j : Fin 3) :
      AnalyticOnNhd ℝ (fun P : Config 9 3 => P v j) univ := by
    exact ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj v : (Fin 9 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))).analyticOnNhd _
  have hlift (v : Fin 9) (j : ℕ) :
      AnalyticOnNhd ℝ (fun P : Config 9 3 => LiftCoord P v j) univ := by
    unfold LiftCoord
    split_ifs
    · exact hcoord _ _
    · exact analyticOnNhd_const
  have hdet {n : ℕ} (f : Config 9 3 → Matrix (Fin n) (Fin n) ℝ)
      (hf : ∀ i j, AnalyticOnNhd ℝ (fun P => f P i j) univ) :
      AnalyticOnNhd ℝ (fun P => (f P).det) univ := by
    intro P hP
    simp only [Matrix.det_apply]
    apply Finset.analyticAt_fun_sum
    intro σ hσ
    exact (Finset.analyticAt_fun_prod _ fun i hi => hf (σ i) i P hP).const_smul
  have hsign (col : Fin 9 → ZMod 3) (v j : Fin 9) :
      AnalyticOnNhd ℝ (fun P : Config 9 3 => SignMatrix P col v j) univ := by
    unfold SignMatrix SignRow
    split_ifs <;> first | exact analyticOnNhd_const | exact hlift _ _ | exact (hlift _ _).neg
  have hsignDet (col : Fin 9 → ZMod 3) :
      AnalyticOnNhd ℝ (fun P : Config 9 3 => (SignMatrix P col).det) univ :=
    hdet _ (hsign col)
  have hcofactor (col : Fin 9 → ZMod 3) (v : Fin 9) :
      AnalyticOnNhd ℝ (fun P : Config 9 3 => LastCofactor (SignMatrix P col) v) univ := by
    exact analyticOnNhd_const.mul (hdet _ fun i j => hsign col _ _)
  have htriple (t : Fin 3 → Fin 9) (q : Config 9 3 → Fin 3 → ℝ)
      (hq : ∀ j, AnalyticOnNhd ℝ (fun P => q P j) univ) :
      AnalyticOnNhd ℝ (fun P : Config 9 3 => TripleDet P t (q P)) univ := by
    apply hdet
    intro i j
    fin_cases i
    · exact (hcoord _ _).sub (hcoord _ _)
    · exact (hcoord _ _).sub (hcoord _ _)
    · exact hq _
  have hq (e : Edge 9) (t t' : Fin 3 → Fin 9) :
      AnalyticOnNhd ℝ (fun P : Config 9 3 => QPoly P e t t') univ := by
    exact ((htriple t _ fun j => (hcoord _ _).sub (hcoord _ _)).mul
      (htriple t' _ fun j => (hcoord _ _).sub (hcoord _ _))).sub
      ((htriple t' _ fun j => (hcoord _ _).sub (hcoord _ _)).mul
      (htriple t _ fun j => (hcoord _ _).sub (hcoord _ _)))
  have hnz (f : Config 9 3 → ℝ) (ha : AnalyticOnNhd ℝ f univ) (hn : f w ≠ 0) :
      IsOpen {P | f P ≠ 0} ∧ Dense {P | f P ≠ 0} := by
    have hc : Continuous f := continuousOn_univ.mp ha.continuousOn
    refine ⟨isOpen_ne.preimage hc, dense_iff_inter_open.mpr ?_⟩
    intro U hU hUne
    obtain ⟨z, hz⟩ := hUne
    by_contra hnone
    have hzero : ∀ P ∈ U, f P = 0 := by
      intro P hP
      by_contra hne
      exact hnone ⟨P, hP, hne⟩
    have hevent : f =ᶠ[𝓝 z] 0 := by
      filter_upwards [hU.mem_nhds hz] with P hP
      exact hzero P hP
    have heq : f = 0 := ha.eq_of_eventuallyEq analyticOnNhd_const hevent
    exact hn (by simpa using congrFun heq w)
  have hfamily {ι : Type} [Finite ι] (f : ι → Config 9 3 → ℝ)
      (ha : ∀ i, AnalyticOnNhd ℝ (f i) univ) (hn : ∀ i, f i w ≠ 0) :
      Dense {P | ∀ i, f i P ≠ 0} ∧ IsOpen {P | ∀ i, f i P ≠ 0} := by
    have he : {P | ∀ i, f i P ≠ 0} = ⋂ i, {P | f i P ≠ 0} := by ext P; simp
    rw [he]
    exact ⟨dense_iInter_of_isOpen (fun i => (hnz _ (ha i) (hn i)).1)
      (fun i => (hnz _ (ha i) (hn i)).2),
      isOpen_iInter_of_finite (fun i => (hnz _ (ha i) (hn i)).1)⟩
  let I1 := {a : Fin 4 → Fin 9 // Function.Injective a}
  let I4 := {s : Edge 9 × (Fin 3 → Fin 9) × (Fin 3 → Fin 9) //
    s.1.1 < s.1.2 ∧ Function.Injective s.2.1 ∧ Function.Injective s.2.2 ∧
    Disjoint (Endpoints s.1) (Finset.univ.image s.2.1) ∧
    Disjoint (Endpoints s.1) (Finset.univ.image s.2.2) ∧
    Disjoint (Finset.univ.image s.2.1) (Finset.univ.image s.2.2)}
  let I9 := {Q : Common.Partition 9 // Q ∈ Universe 3}
  let f1 : I1 → Config 9 3 → ℝ := fun a P =>
    Matrix.det (fun i j : Fin 4 => LiftCoord P (a.val i) j.val)
  let f4 : I4 → Config 9 3 → ℝ := fun s P => QPoly P s.val.1 s.val.2.1 s.val.2.2
  let fs : I9 → Config 9 3 → ℝ := fun Q P => (SignMatrix P (CanonColour Q.val)).det
  let fc : (I9 × Fin 9) → Config 9 3 → ℝ := fun s P =>
    LastCofactor (SignMatrix P (CanonColour s.1.val)) s.2
  have h1 := hfamily f1 (fun a => hdet _ fun i j => hlift _ _)
    (fun a => hw.1 a.val a.property)
  have h4 := hfamily f4 (fun s => hq _ _ _) (fun s =>
    hw.2.1 s.val.1 s.property.1 s.val.2.1 s.val.2.2 s.property.2.1
      s.property.2.2.1 s.property.2.2.2.1 s.property.2.2.2.2.1 s.property.2.2.2.2.2)
  have hs := hfamily fs (fun Q => hsignDet _) (fun Q => (hw.2.2 Q.val Q.property).1)
  have hc := hfamily fc (fun s => hcofactor _ _) (fun s => (hw.2.2 s.1.val s.1.property).2 s.2)
  have he : GenericLocus =
      ({P | ∀ a, f1 a P ≠ 0} ∩ {P | ∀ s, f4 s P ≠ 0}) ∩
      ({P | ∀ Q, fs Q P ≠ 0} ∩ {P | ∀ s, fc s P ≠ 0}) := by
    ext P
    constructor
    · intro hP
      exact ⟨⟨fun a => hP.1 a.val a.property,
          fun s => hP.2.1 s.val.1 s.property.1 s.val.2.1 s.val.2.2 s.property.2.1
            s.property.2.2.1 s.property.2.2.2.1 s.property.2.2.2.2.1 s.property.2.2.2.2.2⟩,
        ⟨fun Q => (hP.2.2 Q.val Q.property).1,
          fun s => (hP.2.2 s.1.val s.1.property).2 s.2⟩⟩
    · rintro ⟨⟨hP1, hP4⟩, ⟨hPs, hPc⟩⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        exact hP1 ⟨a, ha⟩
      · intro e he t t' ht ht' het het' htt'
        exact hP4 ⟨(e, t, t'), he, ht, ht', het, het', htt'⟩
      · intro Q hQ
        exact ⟨hPs ⟨Q, hQ⟩, fun v => hPc (⟨Q, hQ⟩, v)⟩
  rw [he]
  exact ⟨(h1.1.inter_of_isOpen_left h4.1 h1.2).inter_of_isOpen_left
      (hs.1.inter_of_isOpen_left hc.1 hs.2) (h1.2.inter h4.2),
    (h1.2.inter h4.2).inter (hs.2.inter hc.2)⟩
