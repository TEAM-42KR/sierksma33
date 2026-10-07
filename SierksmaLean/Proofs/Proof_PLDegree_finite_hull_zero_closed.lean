import SierksmaLean.Definitions.Def_PLDegree_Chain
set_option autoImplicit false
open PLDegree
open scoped BigOperators

theorem proof_PLDegree_finite_hull_zero_closed {V : Type*} [LinearOrder V] {n : ℕ} (s : Finset V) :
    IsClosed {F : V → Fin n → ℝ | (0 : Fin n → ℝ) ∈ hull F s} := by
  classical
  let W := stdSimplex ℝ s
  let f : (V → Fin n → ℝ) × W → (Fin n → ℝ) :=
    fun p => ∑ i : s, p.2.val i • p.1 i
  have hc : Continuous f := by
    apply continuous_finset_sum
    intro i hi
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
      ((continuous_apply i.val).comp continuous_fst)
  have he : ∀ F : V → Fin n → ℝ,
      (0 : Fin n → ℝ) ∈ hull F s ↔ ∃ w : W, f (F,w)=0 := by
    intro F
    let L : (s → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      ∑ i : s, (LinearMap.proj (R := ℝ) i).smulRight (F i)
    have hL : ∀ w : s → ℝ, L w = ∑ i : s, w i • F i := by
      intro w
      simp [L]
    have hr : (fun i : s => L (Pi.single i 1)) = fun i : s => F i := by
      funext i
      rw [hL]
      simp [Pi.single_apply]
    have hh : hull F s = L '' stdSimplex ℝ s := by
      rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull,
        ← Set.range_comp]
      change convexHull ℝ (F '' (s : Set V)) = convexHull ℝ (Set.range _)
      rw [show (L ∘ (fun i : s => Pi.single i (1 : ℝ))) =
          (fun i : s => F i) from hr]
      congr 1
      ext v
      simp
    rw [hh]
    constructor
    · rintro ⟨w, hw, hzero⟩
      exact ⟨⟨w,hw⟩, (hL w).symm.trans hzero⟩
    · rintro ⟨w, hw⟩
      exact ⟨w.val,w.property,(hL w.val).trans hw⟩
  have himg : {F : V → Fin n → ℝ | (0 : Fin n → ℝ) ∈ hull F s} =
      Prod.fst '' {p : (V → Fin n → ℝ) × W | f p=0} := by
    ext F
    simp only [Set.mem_setOf_eq, Set.mem_image, he]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨(F,w),hw,rfl⟩
    · rintro ⟨⟨F',w⟩,hw,hF⟩
      change F'=F at hF
      subst F'
      exact ⟨w,hw⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ (isClosed_eq hc continuous_const)
