import SierksmaLean.Definitions.Def_PLDegree_Chain
import SierksmaLean.Definitions.Def_PLDegree_AffineRayHit
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import SierksmaLean.Definitions.Def_PLDegree_BoundaryOperator
section

set_option maxHeartbeats 25000
set_option synthInstance.maxHeartbeats 5000
open PLDegree

private theorem PLDegree.ray_det_linear_nonzero {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) (s : Finset V)
    (hs : s.card=n+1) (hd : augmentedDet F s ≠ 0) :
    ∀ v ∈ s, ∃ L : (Fin n → ℝ) →ₗ[ℝ] ℝ,
      L ≠ 0 ∧ ∀ u, L u = rayDet F u (s.erase v) := by
  classical
  intro v hv
  let face := s.erase v
  have hface : face.card = n := by
    dsimp [face]
    rw [Finset.card_erase_of_mem hv, hs]
    omega
  let f : Fin n → V := face.orderEmbOfFin hface
  have hfm : ∀ i, f i ∈ face := fun i => (face.orderEmbOfFin_mem hface i)
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    Fin.cons 0 (fun i => augment (F (f i)) 1)
  have hRM : ∀ u, rayMatrix F u face hface = B.updateRow 0 (augment u 0) := by
    intro u
    ext i j
    cases i using Fin.cases with
    | zero => simp [rayMatrix, B, Matrix.updateRow]
    | succ i => simp [rayMatrix, B, Matrix.updateRow, f, Fin.ext_iff]
  let q : (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) := {
    toFun := fun u => augment u 0
    map_add' := by
      intro u w
      funext j
      simp only [augment, Pi.add_apply]
      split_ifs <;> simp
    map_smul' := by
      intro r u
      funext j
      simp only [augment, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp }
  let D : MultilinearMap ℝ (fun _ : Fin (n+1) => Fin (n+1) → ℝ) ℝ :=
    Matrix.detRowAlternating.toMultilinearMap
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := (D.toLinearMap B 0).comp q
  have hLval : ∀ u, L u = rayDet F u face := by
    intro u
    change (B.updateRow 0 (augment u 0)).det = rayDet F u face
    rw [rayDet, dif_pos hface, hRM]
  let t : Fin (n+1) → V := Fin.cons v f
  have htinj : Function.Injective t := by
    apply Fin.cons_injective_of_injective
    · rintro ⟨i, hi⟩
      have hh := Finset.mem_erase.mp (hfm i)
      exact hh.1 hi
    · exact (face.orderEmbOfFin hface).injective
  have htm : ∀ i, t i ∈ s := by
    intro i
    cases i using Fin.cases with
    | zero => exact hv
    | succ i => exact Finset.mem_of_mem_erase (hfm i)
  let ef : Fin (n+1) → Fin (n+1) := fun i =>
    (s.orderIsoOfFin hs).symm ⟨t i, htm i⟩
  have hefinj : Function.Injective ef := by
    intro i j hij
    apply htinj
    exact congrArg Subtype.val ((s.orderIsoOfFin hs).symm.injective hij)
  let e : Equiv.Perm (Fin (n+1)) :=
    Equiv.ofBijective ef ⟨hefinj, Finite.surjective_of_injective hefinj⟩
  have heval : ∀ i, s.orderEmbOfFin hs (e i) = t i := by
    intro i
    exact congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨t i, htm i⟩)
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i => augment (F (t i)) 1
  have hAeq : A = (augmentedMatrix F s hs).submatrix e id := by
    ext i j
    simp only [Matrix.submatrix_apply, augmentedMatrix, heval]
    rfl
  have hd' : (augmentedMatrix F s hs).det ≠ 0 := by
    simpa only [augmentedDet, dif_pos hs] using hd
  have hAd : A.det ≠ 0 := by
    rw [hAeq, Matrix.det_permute]
    exact mul_ne_zero (by exact_mod_cast (Units.ne_zero e.sign)) hd'
  let i0 : Fin n := ⟨0, by omega⟩
  let u : Fin n → ℝ := F v - F (f i0)
  have hAray : rayMatrix F u face hface =
      A.updateRow 0 (A 0 + (-1 : ℝ) • A i0.succ) := by
    ext i j
    cases i using Fin.cases with
    | zero =>
      simp only [rayMatrix, Fin.val_zero, dite_true, Matrix.updateRow_self]
      dsimp [u, A, t]
      simp only [Fin.cons_zero, Fin.cons_succ, augment, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      split_ifs <;> ring
    | succ i =>
      simp [rayMatrix, Matrix.updateRow, A, t, f, Fin.ext_iff]
  have huray : rayDet F u face ≠ 0 := by
    rw [rayDet, dif_pos hface, hAray, Matrix.det_updateRow_add_smul_self A (i := 0) (j := i0.succ) (Ne.symm (Fin.succ_ne_zero i0)) (-1 : ℝ)]
    exact hAd
  refine ⟨L, ?_, ?_⟩
  · intro hzero
    have hu0 : L u = 0 := by rw [hzero]; rfl
    exact huray (by rwa [hLval u] at hu0)
  · intro w
    exact hLval w

open PLDegree

private theorem PLDegree.lower_face_span_proper {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (t : Finset V) (ht : t.card < n) :
    Submodule.span ℝ (F '' (t : Set V)) ≠ ⊤ := by
  classical
  have H : Module.finrank ℝ (Submodule.span ℝ (F '' (t : Set V))) ≤ t.card := by
    calc
      _ = ((t.image F : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)).finrank ℝ := by
        rw [Finset.coe_image]
        rfl
      _ ≤ (t.image F).card := finrank_span_finset_le_card (R := ℝ) _
      _ ≤ t.card := Finset.card_image_le
  intro heq
  rw [heq, finrank_top] at H
  have H' : n ≤ t.card := by simpa using H
  exact (not_lt_of_ge H') ht

open PLDegree

private theorem PLDegree.ray_hits_mem_span {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (u : Fin n → ℝ) (s : Finset V)
    (h : RayHits F u s) : u ∈ Submodule.span ℝ (F '' (s : Set V)) := by
  rcases h with ⟨t, ht, hh⟩
  let p := Submodule.span ℝ (F '' (s : Set V))
  have hincl : hull F s ⊆ (p : Set (Fin n → ℝ)) := by
    exact convexHull_min (fun x hx => Submodule.subset_span hx) p.convex
  have htmem : t • u ∈ p := hincl hh
  exact (p.smul_mem_iff (ne_of_gt ht)).mp htmem

open PLDegree

private theorem PLDegree.generic_common_ray {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) (ss : Finset (Finset V))
    (h : ∀ s ∈ ss, s.card=n+1 ∧ augmentedDet F s ≠ 0) :
    ∃ u : Fin n → ℝ, ∀ s ∈ ss, RayGeneric F u s := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  letI : Nonempty (Fin n) := ⟨i0⟩
  let facets : Finset (Finset V × V) := ss.biUnion (fun s => s.image (fun v => (s,v)))
  have hfac : ∀ s v, (s,v) ∈ facets ↔ s ∈ ss ∧ v ∈ s := by
    intro s v
    simp [facets]
  have hf : ∀ x : facets, ∃ L : (Fin n → ℝ) →ₗ[ℝ] ℝ,
      L ≠ 0 ∧ ∀ u, L u = rayDet F u (x.val.1.erase x.val.2) := by
    intro x
    have hx := (hfac x.val.1 x.val.2).mp x.property
    exact PLDegree.ray_det_linear_nonzero hn F x.val.1 (h _ hx.1).1 (h _ hx.1).2 x.val.2 hx.2
  choose L hLn hLval using hf
  let lower : Finset (Finset V) := ss.biUnion (fun s => s.powerset.filter (fun t => t.card < n))
  have hlo : ∀ t ∈ lower, t.card < n := by
    intro t ht
    rcases Finset.mem_biUnion.mp ht with ⟨s, _, ht⟩
    exact (Finset.mem_filter.mp ht).2
  let I := Sum facets (Sum lower Unit)
  let p : I → Submodule ℝ (Fin n → ℝ) := Sum.elim (fun x => (L x).ker)
    (Sum.elim (fun t => Submodule.span ℝ (F '' (t.val : Set V))) (fun _ => ⊥))
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i
    cases i with
    | inl x =>
      change (L x).ker ≠ ⊤
      intro htop
      apply hLn x
      apply LinearMap.ext
      intro v
      have hv : v ∈ (L x).ker := htop ▸ Submodule.mem_top
      exact hv
    | inr j =>
      cases j with
      | inl t =>
        exact PLDegree.lower_face_span_proper F t.val (hlo t.val t.property)
      | inr j =>
        change (⊥ : Submodule ℝ (Fin n → ℝ)) ≠ ⊤
        exact bot_ne_top
  obtain ⟨u, hu⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨u, ?_⟩
  intro s hs
  refine ⟨?_, ?_, ?_⟩
  · have hx := hu (Sum.inr (Sum.inr ()))
    simpa [p] using hx
  · intro v hv
    let x : facets := ⟨(s,v), (hfac s v).mpr ⟨hs,hv⟩⟩
    have hx := hu (Sum.inl x)
    change u ∉ (L x).ker at hx
    rw [LinearMap.mem_ker, hLval x u] at hx
    convert hx using 1
    congr 1
    ext w
    simp only [Finset.mem_erase]
    rfl
  · intro t ht hcard hit
    have htn : t.card < n := by have hc := (h s hs).1; omega
    have htl : t ∈ lower := Finset.mem_biUnion.mpr ⟨s, hs, by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨ht,htn⟩⟩
    let x : lower := ⟨t,htl⟩
    have hx := hu (Sum.inr (Sum.inl x))
    exact hx (PLDegree.ray_hits_mem_span F u t hit)
end

section
open scoped BigOperators
open PLDegree
set_option maxHeartbeats 800000

private theorem PLDegree.affine_interval_balance {n : ℕ} (a b : Fin (n+1) → ℝ)
    (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 0)
    (hg : IntervalGeneric a b) :
    AffineSlopeSum a b = -(@ite ℤ (PositiveAtZero a)
      (Classical.propDecidable _) 1 0) := by
  classical
  rcases hg with ⟨hbn, hzero, hcorner⟩
  let r : Fin (n+1) → ℝ := fun i => -a i / b i
  have hr (i : Fin (n+1)) : a i + r i * b i = 0 := by
    dsimp [r]
    rw [div_mul_cancel₀ _ (hbn i)]
    ring
  have hroot (i : Fin (n+1)) (t : ℝ) (hz : a i + t * b i = 0) : t = r i := by
    have he : (t - r i) * b i = 0 := by nlinarith [hr i]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (hbn i))
  have hexneg : ∃ i, b i < 0 := by
    by_contra hn
    push_neg at hn
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hn i)).mp hb
    exact hbn 0 (hz 0 (Finset.mem_univ 0))
  have hexpos : ∃ i, 0 < b i := by
    by_contra hn
    push_neg at hn
    have hs : ∑ i, -b i = 0 := by rw [Finset.sum_neg_distrib, hb, neg_zero]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => neg_nonneg.mpr (hn i))).mp hs
    have he : b (0 : Fin (n+1)) = 0 := by simpa using hz 0 (Finset.mem_univ 0)
    exact hbn 0 he
  let P := Finset.univ.filter (fun i => 0 < b i)
  let N := Finset.univ.filter (fun i => b i < 0)
  have hP : P.Nonempty := by
    obtain ⟨i, hi⟩ := hexpos
    exact ⟨i, by simp [P, hi]⟩
  have hN : N.Nonempty := by
    obtain ⟨i, hi⟩ := hexneg
    exact ⟨i, by simp [N, hi]⟩
  obtain ⟨p, hpP, hpmax⟩ := Finset.exists_max_image P r hP
  obtain ⟨q, hqN, hqmin⟩ := Finset.exists_min_image N r hN
  have hbp : 0 < b p := (Finset.mem_filter.mp hpP).2
  have hbq : b q < 0 := (Finset.mem_filter.mp hqN).2
  have hpq : p ≠ q := by intro he; subst q; linarith
  have hp (i : Fin (n+1)) (hi : 0 < b i) : r i ≤ r p :=
    hpmax i (by simp [P, hi])
  have hq (i : Fin (n+1)) (hi : b i < 0) : r q ≤ r i :=
    hqmin i (by simp [N, hi])
  have hpos (i : Fin (n+1)) (hi : 0 < b i) (t : ℝ) :
      0 ≤ a i + t * b i ↔ r i ≤ t := by
    constructor
    · intro ht
      by_contra hn
      have hm : (t - r i) * b i < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge hn)) hi
      nlinarith [hr i]
    · intro ht
      have hm := mul_nonneg (sub_nonneg.mpr ht) hi.le
      nlinarith [hr i]
  have hneg (i : Fin (n+1)) (hi : b i < 0) (t : ℝ) :
      0 ≤ a i + t * b i ↔ t ≤ r i := by
    constructor
    · intro ht
      by_contra hn
      have hm : (t - r i) * b i < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_not_ge hn)) hi
      nlinarith [hr i]
    · intro ht
      have hm := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ht) hi.le
      nlinarith [hr i]
  have hfeas (t : ℝ) : (∀ i, 0 ≤ a i + t * b i) ↔ r p ≤ t ∧ t ≤ r q := by
    constructor
    · intro hf
      exact ⟨(hpos p hbp t).mp (hf p), (hneg q hbq t).mp (hf q)⟩
    · rintro ⟨hl, hu⟩ i
      rcases lt_or_gt_of_ne (hbn i) with hn | hn
      · exact (hneg i hn t).mpr (hu.trans (hq i hn))
      · exact (hpos i hn t).mpr ((hp i hn).trans hl)
  have hsupport (i : Fin (n+1)) (hi : AffineRayHit a b i) : i = p ∨ i = q := by
    obtain ⟨t, ht, hzi, hf⟩ := hi
    have htr := hroot i t hzi
    have hbds := (hfeas t).mp hf
    rcases lt_or_gt_of_ne (hbn i) with hn | hn
    · right
      have htq : t = r q := le_antisymm hbds.2 (by simpa [← htr] using hq i hn)
      by_contra hne
      apply hcorner t ht hf i q hne
      exact ⟨hzi, by simpa [htq] using hr q⟩
    · left
      have htp : t = r p := le_antisymm (by simpa [← htr] using hp i hn) hbds.1
      by_contra hne
      apply hcorner t ht hf i p hne
      exact ⟨hzi, by simpa [htp] using hr p⟩
  have hphit : AffineRayHit a b p ↔ 0 < r p ∧ r p ≤ r q := by
    constructor
    · rintro ⟨t, ht, hz, hf⟩
      have ht' := hroot p t hz
      exact ⟨by simpa [ht'] using ht, by simpa [ht'] using ((hfeas t).mp hf).2⟩
    · rintro ⟨ht, hpu⟩
      exact ⟨r p, ht, hr p, (hfeas (r p)).mpr ⟨le_rfl, hpu⟩⟩
  have hqhit : AffineRayHit a b q ↔ 0 < r q ∧ r p ≤ r q := by
    constructor
    · rintro ⟨t, ht, hz, hf⟩
      have ht' := hroot q t hz
      exact ⟨by simpa [ht'] using ht, by simpa [ht'] using ((hfeas t).mp hf).1⟩
    · rintro ⟨ht, hpu⟩
      exact ⟨r q, ht, hr q, (hfeas (r q)).mpr ⟨hpu, le_rfl⟩⟩
  have hsum : AffineSlopeSum a b =
      (if AffineRayHit a b p then (1 : ℤ) else 0) +
      (if AffineRayHit a b q then (-1 : ℤ) else 0) := by
    unfold AffineSlopeSum
    calc
      ∑ i, (if AffineRayHit a b i then (SignType.sign (b i) : ℤ) else 0) =
          ∑ i, ((if i = p then (if AffineRayHit a b p then (1 : ℤ) else 0) else 0) +
          (if i = q then (if AffineRayHit a b q then (-1 : ℤ) else 0) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hip : i = p
        · subst i
          simp [hpq, sign_pos hbp]
        · by_cases hiq : i = q
          · subst i
            simp [Ne.symm hpq, sign_neg hbq]
          · have hn : ¬ AffineRayHit a b i := fun h => (hsupport i h).elim hip hiq
            simp [hip, hiq, hn]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hZbounds (hz : PositiveAtZero a) : r p ≤ 0 ∧ 0 ≤ r q := by
    apply (hfeas 0).mp
    intro i
    simpa using (hz i).le
  have hZupper (hz : PositiveAtZero a) : 0 < r q := by
    by_contra hn
    have hm : 0 ≤ r q * b q := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hn) hbq.le
    have ha := hz q
    nlinarith [hr q]
  by_cases hpu : r p ≤ r q
  · by_cases hu : 0 < r q
    · have hqh : AffineRayHit a b q := hqhit.mpr ⟨hu, hpu⟩
      by_cases hl : 0 < r p
      · have hph : AffineRayHit a b p := hphit.mpr ⟨hl, hpu⟩
        have hnZ : ¬ PositiveAtZero a := fun hz => (not_le_of_gt hl) (hZbounds hz).1
        rw [hsum, if_pos hph, if_pos hqh, if_neg hnZ]
        norm_num
      · have hnph : ¬ AffineRayHit a b p := fun h => hl (hphit.mp h).1
        have hZ : PositiveAtZero a := hzero (by
          have hf := (hfeas 0).mpr ⟨le_of_not_gt hl, hu.le⟩
          simpa using hf)
        rw [hsum, if_neg hnph, if_pos hqh, if_pos hZ]
        norm_num
    · have hnph : ¬ AffineRayHit a b p := by
        intro h
        obtain ⟨hl, hbnd⟩ := hphit.mp h
        exact hu (hl.trans_le hbnd)
      have hnqh : ¬ AffineRayHit a b q := fun h => hu (hqhit.mp h).1
      have hnZ : ¬ PositiveAtZero a := fun hz => hu (hZupper hz)
      rw [hsum, if_neg hnph, if_neg hnqh, if_neg hnZ]
      norm_num
  · have hnph : ¬ AffineRayHit a b p := fun h => hpu (hphit.mp h).2
    have hnqh : ¬ AffineRayHit a b q := fun h => hpu (hqhit.mp h).2
    have hnZ : ¬ PositiveAtZero a := fun hz => hpu ((hZbounds hz).1.trans (hZbounds hz).2)
    rw [hsum, if_neg hnph, if_neg hnqh, if_neg hnZ]
    norm_num
end

section
set_option autoImplicit false
open scoped BigOperators
open PLDegree
set_option maxHeartbeats 1000000

section HullReuse

private theorem PLDegree.affine_coordinates_hull {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (hs : s.card=n+1)
    (hd : augmentedDet F s ≠ 0) (t : Finset V) (ht : t ⊆ s) (x : Fin n → ℝ) :
    let c := Matrix.vecMul (augment x 1) (augmentedMatrix F s hs)⁻¹
    x ∈ hull F t ↔ (∀ i, 0 ≤ c i) ∧
      (∀ i, s.orderEmbOfFin hs i ∉ t → c i = 0) := by
  classical
  let M := augmentedMatrix F s hs
  let e := s.orderEmbOfFin hs
  let c : (Fin n → ℝ) → Fin (n+1) → ℝ := fun y => Matrix.vecMul (augment y 1) M⁻¹
  change x ∈ hull F t ↔ (∀ i, 0 ≤ c x i) ∧ (∀ i, e i ∉ t → c x i = 0)
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (by simpa [augmentedDet, hs, M] using hd)
  have heq (y : Fin n → ℝ) : Matrix.vecMul (c y) M = augment y 1 := by
    dsimp [c]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M hM, Matrix.vecMul_one]
  have hsum (y : Fin n → ℝ) : ∑ i, c y i = 1 := by
    have hh := congrFun (heq y) (Fin.last n)
    simpa [M, Matrix.vecMul, dotProduct, augmentedMatrix, augment] using hh
  have hrepr (y : Fin n → ℝ) : ∑ i, c y i • F (e i) = y := by
    funext k
    have hh := congrFun (heq y) k.castSucc
    simpa [M, e, Matrix.vecMul, dotProduct, augmentedMatrix, augment,
      k.isLt, Finset.sum_apply, Pi.smul_apply] using hh
  have hvertex (j : Fin (n+1)) : c (F (e j)) = Pi.single j 1 := by
    have hj : augment (F (e j)) 1 = Matrix.vecMul (Pi.single j 1) M := by
      rw [Matrix.single_one_vecMul]
      rfl
    dsimp [c]
    rw [hj, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hM, Matrix.vecMul_one]
  have hccombo (y z : Fin n → ℝ) (r q : ℝ) (hrq : r+q=1) :
      c (r • y + q • z) = r • c y + q • c z := by
    have hau : augment (r • y + q • z) 1 = r • augment y 1 + q • augment z 1 := by
      funext j
      dsimp [augment]
      split_ifs with hj
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · simpa using hrq.symm
    dsimp [c]
    rw [hau, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul]
  constructor
  · intro hx
    let C : Set (Fin n → ℝ) := {y | (∀ i, 0 ≤ c y i) ∧ (∀ i, e i ∉ t → c y i = 0)}
    have hsub : F '' (t : Set V) ⊆ C := by
      rintro y ⟨v, hv, rfl⟩
      obtain ⟨j, hj⟩ : ∃ j, e j = v := by
        have hv' : v ∈ s := ht hv
        exact ⟨(s.orderIsoOfFin hs).symm ⟨v, hv'⟩, by simp [e, ← Finset.coe_orderIsoOfFin_apply]⟩
      subst v
      change (∀ i, 0 ≤ c (F (e j)) i) ∧ (∀ i, e i ∉ t → c (F (e j)) i = 0)
      rw [hvertex]
      constructor
      · intro i
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · intro i hi
        have hne : i ≠ j := by intro hij; subst i; exact hi hv
        simp [Pi.single_apply, hne, Ne.symm hne]
    have hconv : Convex ℝ C := by
      intro y hy z hz r q hr hq hrq
      change (∀ i, 0 ≤ c (r • y + q • z) i) ∧
        (∀ i, e i ∉ t → c (r • y + q • z) i = 0)
      rw [hccombo y z r q hrq]
      exact ⟨fun i => add_nonneg (mul_nonneg hr (hy.1 i)) (mul_nonneg hq (hz.1 i)),
        fun i hi => by simp [Pi.add_apply, Pi.smul_apply, hy.2 i hi, hz.2 i hi]⟩
    exact convexHull_min hsub hconv hx
  · rintro ⟨hnonneg, hsupport⟩
    let I := Finset.univ.filter (fun i => e i ∈ t)
    have hIsum : ∑ i ∈ I, c x i = 1 := by
      rw [← hsum x]
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i _ hi
      exact hsupport i (by simpa [I] using hi)
    have hIrepr : ∑ i ∈ I, c x i • F (e i) = x := by
      calc
        ∑ i ∈ I, c x i • F (e i) = ∑ i, c x i • F (e i) := by
          apply Finset.sum_subset (Finset.subset_univ I)
          intro i _ hi
          rw [hsupport i (by simpa [I] using hi), zero_smul]
        _ = x := hrepr x
    have hcm := I.centerMass_mem_convexHull (fun i (_ : i ∈ I) => hnonneg i)
      (show 0 < ∑ i ∈ I, c x i by rw [hIsum]; norm_num)
      (fun i hi => Set.mem_image_of_mem F ((Finset.mem_filter.mp hi).2))
    simpa [hull, Finset.centerMass_eq_of_sum_1 _ _ hIsum, hIrepr] using hcm
end HullReuse

section CramerReuse
attribute [local instance] Classical.propDecidable

private theorem PLDegree.ray_det_cramer {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (hs : s.card=n+1)
    (hd : augmentedDet F s ≠ 0) (u : Fin n → ℝ) (i : Fin (n+1)) :
    (Matrix.vecMul (augment u 0) (augmentedMatrix F s hs)⁻¹) i * augmentedDet F s =
      (incidence s (s.orderEmbOfFin hs i) : ℝ) *
        rayDet F u (s.erase (s.orderEmbOfFin hs i)) := by
  let A := augmentedMatrix F s hs
  let r := augment u 0
  let v := s.orderEmbOfFin hs i
  have hv : v ∈ s := Finset.orderEmbOfFin_mem s hs i
  have ht : (s.erase v).card = n := by
    rw [Finset.card_erase_of_mem hv, hs]
    omega
  have he : (fun j : Fin n => s.orderEmbOfFin hs (i.succAbove j)) =
      (s.erase v).orderEmbOfFin ht := by
    apply Finset.orderEmbOfFin_unique ht
    · intro j
      exact Finset.mem_erase.mpr
        ⟨fun h => Fin.succAbove_ne i j ((s.orderEmbOfFin hs).injective h),
          Finset.orderEmbOfFin_mem s hs _⟩
    · exact (s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove i)
  have hrank : rank s v = i.val := by
    unfold rank v
    calc
      (s.filter (fun w => w < s.orderEmbOfFin hs i)).card =
          ((Finset.Iio i).image (s.orderEmbOfFin hs)).card := by
        congr 1
        ext w
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
        constructor
        · rintro ⟨hw, hlt⟩
          obtain ⟨j, rfl⟩ := (show w ∈ Set.range (s.orderEmbOfFin hs) by
            simpa using hw)
          exact ⟨j, (s.orderEmbOfFin hs).lt_iff_lt.mp hlt, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨Finset.orderEmbOfFin_mem s hs j,
            (s.orderEmbOfFin hs).strictMono hj⟩
      _ = i.val := by
        rw [Finset.card_image_of_injective _ (s.orderEmbOfFin hs).injective]
        exact Fin.card_Iio i
  have hdet : augmentedDet F s = A.det := by
    simp only [augmentedDet, dif_pos hs, A]
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (hdet ▸ hd)
  have hcramer : (Matrix.vecMul r A⁻¹) i * A.det = (A.updateRow i r).det := by
    have h := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose A r hunit) i
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_transpose_apply, mul_comm] using h
  have hmat : rayMatrix F u (s.erase v) ht =
      (A.updateRow i r).submatrix i.cycleRange.symm id := by
    ext j k
    cases j using Fin.cases with
    | zero => simp [rayMatrix, Matrix.submatrix_apply, r]
    | succ j =>
      rw [Matrix.submatrix_apply, Fin.cycleRange_symm_succ,
        Matrix.updateRow_ne (Fin.succAbove_ne i j)]
      simp only [id_eq, A, augmentedMatrix]
      simp [rayMatrix, ← congrFun he j]
  have hsign : ((Equiv.Perm.sign i.cycleRange.symm : ℤ) : ℝ) =
      (incidence s v : ℝ) := by
    rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp [incidence, hrank]
  have hperm : rayDet F u (s.erase v) =
      (incidence s v : ℝ) * (A.updateRow i r).det := by
    rw [rayDet, dif_pos ht, hmat, Matrix.det_permute, hsign]
  have hsquare : (incidence s v : ℝ) * (incidence s v : ℝ) = 1 := by
    simp only [incidence, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [← mul_pow]
    norm_num
  rw [hdet, hcramer]
  change (A.updateRow i r).det = (incidence s v : ℝ) * rayDet F u (s.erase v)
  rw [hperm, ← mul_assoc, hsquare, one_mul]

end CramerReuse

private theorem PLDegree.simplex_ray_affine_bridge {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) (s : Finset V)
    (hs : s.card=n+1) (hd : augmentedDet F s ≠ 0)
    (hz : NoBoundaryZero F s) (u : Fin n → ℝ) (hu : RayGeneric F u s) :
    let a := barycentric F s hs
    let b := Matrix.vecMul (augment u 0) (augmentedMatrix F s hs)⁻¹
    (∑ i, a i = 1) ∧ (∑ i, b i = 0) ∧ IntervalGeneric a b ∧
      (∑ v ∈ s, incidence s v * rayWeight F u (s.erase v)) =
        (SignType.sign (augmentedDet F s) : ℤ) * AffineSlopeSum a b := by
  classical
  let M := augmentedMatrix F s hs
  let e := s.orderEmbOfFin hs
  let a := barycentric F s hs
  let b := Matrix.vecMul (augment u 0) M⁻¹
  change (∑ i, a i = 1) ∧ (∑ i, b i = 0) ∧ IntervalGeneric a b ∧ _
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (by simpa [augmentedDet, hs, M] using hd)
  have he (i : Fin (n+1)) : e i ∈ s := s.orderEmbOfFin_mem hs i
  have heinj : Function.Injective e := e.injective
  have hau (t : ℝ) : augment (t • u) 1 = originRow n + t • augment u 0 := by
    funext j
    by_cases hj : j.val < n
    · have hjne : j ≠ Fin.last n := by intro h; subst j; simpa using hj
      simp [augment, hj, originRow, Pi.single_apply, hjne, Ne.symm hjne,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · have hjlast : j = Fin.last n := Fin.ext (by change j.val = n; have hjlt := j.isLt; omega)
      subst j
      simp [augment, originRow]
  have hcoord (t : ℝ) : Matrix.vecMul (augment (t • u) 1) M⁻¹ = a + t • b := by
    rw [hau t, Matrix.add_vecMul, Matrix.smul_vecMul]
    rfl
  have hco (t : ℝ) (T : Finset V) (hT : T ⊆ s) :
      (t • u) ∈ hull F T ↔
        (∀ i, 0 ≤ a i + t * b i) ∧ (∀ i, e i ∉ T → a i + t * b i = 0) := by
    have h := affine_coordinates_hull F s hs hd T hT (t • u)
    change (t • u) ∈ hull F T ↔ (∀ i, 0 ≤ Matrix.vecMul (augment (t • u) 1) M⁻¹ i) ∧
      (∀ i, e i ∉ T → Matrix.vecMul (augment (t • u) 1) M⁻¹ i = 0) at h
    rw [hcoord] at h
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have hasum : ∑ i, a i = 1 := by
    have heq : Matrix.vecMul a M = originRow n := by
      dsimp [a, barycentric]
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M hM, Matrix.vecMul_one]
    have hh := congrFun heq (Fin.last n)
    simpa [M, Matrix.vecMul, dotProduct, augmentedMatrix, augment, originRow] using hh
  have hbsum : ∑ i, b i = 0 := by
    have heq : Matrix.vecMul b M = augment u 0 := by
      dsimp [b]
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M hM, Matrix.vecMul_one]
    have hh := congrFun heq (Fin.last n)
    simpa [M, Matrix.vecMul, dotProduct, augmentedMatrix, augment] using hh
  have hcr (i : Fin (n+1)) : b i * augmentedDet F s =
      (incidence s (e i) : ℝ) * rayDet F u (s.erase (e i)) :=
    by
      convert ray_det_cramer F s hs hd u i using 1
      congr 2
      ext v
      simp [e, Finset.mem_erase]
  have hinc (i : Fin (n+1)) : (incidence s (e i) : ℝ) ≠ 0 := by
    simp [incidence]
  have hbn (i : Fin (n+1)) : b i ≠ 0 := by
    intro hbi
    have hc := hcr i
    rw [hbi, zero_mul] at hc
    have hrd : rayDet F u (s.erase (e i)) = 0 := (mul_eq_zero.mp hc.symm).resolve_left (hinc i)
    exact hu.2.1 (e i) (he i) (by
      convert hrd using 1
      congr 1
      ext v
      simp only [Finset.mem_erase])
  have hsign (i : Fin (n+1)) :
      incidence s (e i) * (SignType.sign (rayDet F u (s.erase (e i))) : ℤ) =
        (SignType.sign (augmentedDet F s) : ℤ) * (SignType.sign (b i) : ℤ) := by
    have hi : (SignType.sign (incidence s (e i) : ℝ) : ℤ) = incidence s (e i) := by
      simp [incidence, sign_pow]
    have hc := congrArg (fun x : ℝ => (SignType.sign x : ℤ)) (hcr i)
    rw [sign_mul, sign_mul, SignType.coe_mul, SignType.coe_mul, hi] at hc
    simpa only [mul_comm] using hc.symm
  have hout (T : Finset V) (i : Fin (n+1)) (hi : e i ∈ T) (j : Fin (n+1))
      (hj : e j ∉ T.erase (e i)) (hjT : e j ∈ T) : j = i := by
    apply heinj
    by_contra hne
    exact hj (Finset.mem_erase.mpr ⟨hne, hjT⟩)
  have hhit (i : Fin (n+1)) : RayHits F u (s.erase (e i)) ↔ AffineRayHit a b i := by
    constructor
    · rintro ⟨t, ht, hx⟩
      have hc := (hco t (s.erase (e i)) (Finset.erase_subset _ _)).mp hx
      exact ⟨t, ht, hc.2 i (Finset.notMem_erase _ _), hc.1⟩
    · rintro ⟨t, ht, hz, hnonneg⟩
      refine ⟨t, ht, (hco t (s.erase (e i)) (Finset.erase_subset _ _)).mpr ⟨hnonneg, ?_⟩⟩
      intro j hj
      have hji := hout s i (he i) j hj (he j)
      simpa [hji] using hz
  have hzerogen : (∀ i, 0 ≤ a i) → PositiveAtZero a := by
    intro hnonneg i
    by_contra hi
    have hai : a i = 0 := le_antisymm (le_of_not_gt hi) (hnonneg i)
    apply hz (s.erase (e i)) (Finset.erase_ssubset (he i))
    have hmem := (hco 0 (s.erase (e i)) (Finset.erase_subset _ _)).mpr
      ⟨fun j => by simpa using hnonneg j, fun j hj => by
        have hji := hout s i (he i) j hj (he j)
        simpa [hji] using hai⟩
    simpa using hmem
  have hcorner : ∀ t : ℝ, 0 < t → (∀ k, 0 ≤ a k + t * b k) →
      ∀ i j : Fin (n+1), i ≠ j → ¬ (a i + t * b i = 0 ∧ a j + t * b j = 0) := by
    intro t ht hnonneg i j hij ⟨hzi, hzj⟩
    let T := (s.erase (e i)).erase (e j)
    have heji : e j ≠ e i := fun h => hij (heinj h).symm
    have hjmem : e j ∈ s.erase (e i) := Finset.mem_erase.mpr ⟨heji, he j⟩
    have hTsub : T ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hTcard : T.card + 2 ≤ s.card := by
      have hc₁ := Finset.card_erase_of_mem (he i)
      have hc₂ := Finset.card_erase_of_mem hjmem
      dsimp [T]
      omega
    apply hu.2.2 T hTsub hTcard
    refine ⟨t, ht, (hco t T hTsub).mpr ⟨hnonneg, ?_⟩⟩
    intro k hk
    by_cases hki : k = i
    · simpa [hki] using hzi
    · by_cases hkj : k = j
      · simpa [hkj] using hzj
      · exfalso
        exact hk (Finset.mem_erase.mpr ⟨fun h => hkj (heinj h),
          Finset.mem_erase.mpr ⟨fun h => hki (heinj h), he k⟩⟩)
  refine ⟨hasum, hbsum, ⟨hbn, hzerogen, hcorner⟩, ?_⟩
  let w : V → ℤ := fun v => incidence s v * rayWeight F u (s.erase v)
  have hsumorder : ∑ v ∈ s, w v = ∑ i, w (e i) := by
    rw [← s.map_orderEmbOfFin_univ hs, Finset.sum_map]
    rfl
  change ∑ v ∈ s, w v = (SignType.sign (augmentedDet F s) : ℤ) * AffineSlopeSum a b
  rw [hsumorder, AffineSlopeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [w]
  rw [rayWeight, hhit i]
  by_cases hi : AffineRayHit a b i
  · simpa [hi] using hsign i
  · simp [hi]
end

section
open scoped BigOperators
open PLDegree

private theorem PLDegree.simplex_ray_formula {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) :
    (∀ s : Finset V, s.card=n+1 → augmentedDet F s ≠ 0 → NoBoundaryZero F s →
      (∃ u : Fin n → ℝ, RayGeneric F u s) ∧
      ∀ u : Fin n → ℝ, RayGeneric F u s →
        simplexDegree F s = - ∑ v ∈ s, incidence s v * rayWeight F u (s.erase v)) ∧
    (∀ ss : Finset (Finset V),
      (∀ s ∈ ss, s.card=n+1 ∧ augmentedDet F s ≠ 0 ∧ NoBoundaryZero F s) →
      ∃ u : Fin n → ℝ, ∀ s ∈ ss, RayGeneric F u s) := by
  classical
  constructor
  · intro s hs hd hz
    obtain ⟨u, hu⟩ := PLDegree.generic_common_ray hn F {s} (by
      intro t ht
      simpa only [Finset.mem_singleton.mp ht] using And.intro hs hd)
    refine ⟨⟨u, hu s (by simp)⟩, ?_⟩
    intro u hu
    let a := barycentric F s hs
    let b := Matrix.vecMul (augment u 0) (augmentedMatrix F s hs)⁻¹
    have hbridge := PLDegree.simplex_ray_affine_bridge hn F s hs hd hz u hu
    change (∑ i, a i = 1) ∧ (∑ i, b i = 0) ∧ IntervalGeneric a b ∧
      (∑ v ∈ s, incidence s v * rayWeight F u (s.erase v)) =
        (SignType.sign (augmentedDet F s) : ℤ) * AffineSlopeSum a b at hbridge
    have hib := PLDegree.affine_interval_balance a b hbridge.1 hbridge.2.1 hbridge.2.2.1
    have hd' : (augmentedMatrix F s hs).det ≠ 0 := by
      simpa only [augmentedDet, dif_pos hs] using hd
    have hdeg : simplexDegree F s = (SignType.sign (augmentedDet F s) : ℤ) *
        (if PositiveAtZero a then 1 else 0) := by
      unfold simplexDegree
      rw [dif_pos hs]
      by_cases hp : PositiveAtZero a
      · rw [if_pos ⟨hd', hp⟩, if_pos hp]
        simp only [mul_one, augmentedDet, dif_pos hs]
      · rw [if_neg (by rintro ⟨_, h⟩; exact hp h), if_neg hp]
        simp
    rw [hdeg, hbridge.2.2.2, hib]
    ring
  · intro ss h
    exact PLDegree.generic_common_ray hn F ss (fun s hs => ⟨(h s hs).1, (h s hs).2.1⟩)
end

section
open scoped BigOperators Matrix

private theorem PLDegree.nonsingular_rows_zero_free {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0) :
    (0 : Fin n → ℝ) ∉ convexHull ℝ (Set.range (fun i => M i)) := by
  classical
  let L : Fin n → ℝ := M⁻¹ *ᵥ (fun _ => 1)
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun v => ∑ i, v i * L i
    map_add' := by intro v z; simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by intro a v; simp [mul_assoc, Finset.mul_sum] }
  have hh : M *ᵥ L = (fun _ => 1) := by
    dsimp [L]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  have hrow (i : Fin n) : f (M i) = 1 := congrFun hh i
  have hs : Set.range (fun i => M i) ⊆ f ⁻¹' ({1} : Set ℝ) := by
    rintro x ⟨i, rfl⟩
    exact hrow i
  have hc : Convex ℝ (f ⁻¹' ({1} : Set ℝ)) := (convex_singleton (1 : ℝ)).linear_preimage f
  intro h0
  have bad := convexHull_min hs hc h0
  have hz : f 0 = 0 := f.map_zero
  change f 0 = 1 at bad
  rw [hz] at bad
  exact zero_ne_one bad
end

section
open scoped BigOperators
open PLDegree
attribute [local instance] Classical.propDecidable

private theorem PLDegree.simplex_gp_no_boundary_zero {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (h : SimplexGP F s) : NoBoundaryZero F s := by
  rcases h with ⟨hs, hd, hface⟩
  intro t ht hz
  obtain ⟨v, hvs, hvt⟩ := Finset.exists_of_ssubset ht
  have he : (s.erase v).card=n := by
    rw [Finset.card_erase_of_mem hvs, hs]
    omega
  have hM : Matrix.det (fun i j : Fin n => F ((s.erase v).orderEmbOfFin he i) j) ≠ 0 := by
    have hh := hface v hvs
    simpa only [linearDet, dif_pos he] using hh
  have hr : Set.range (fun i : Fin n => F ((s.erase v).orderEmbOfFin he i)) =
      F '' (s.erase v : Set V) := by
    change Set.range (F ∘ (s.erase v).orderEmbOfFin he) = _
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have hsub : t ⊆ s.erase v := Finset.subset_erase.mpr ⟨ht.1, hvt⟩
  have hz' : (0 : Fin n → ℝ) ∈ convexHull ℝ (F '' (s.erase v : Set V)) :=
    convexHull_mono (Set.image_mono (show (t : Set V) ⊆ (s.erase v : Set V) from hsub)) hz
  rw [← hr] at hz'
  exact PLDegree.nonsingular_rows_zero_free _ hM hz'
end

section
open scoped BigOperators
open PLDegree

private theorem PLDegree.chain_linearity {V : Type*} [LinearOrder V] :
    (∀ c d : Chain V, boundary (c+d)=boundary c+boundary d) ∧
    (∀ c d : Chain V, boundary (c-d)=boundary c-boundary d) ∧
    (∀ a : ℤ, ∀ c : Chain V, boundary (a • c)=a • boundary c) ∧
    (∀ y : V, ∀ c d : Chain V, cone y (c+d)=cone y c+cone y d) ∧
    (∀ y : V, ∀ c d : Chain V, cone y (c-d)=cone y c-cone y d) ∧
    (∀ y : V, ∀ a : ℤ, ∀ c : Chain V, cone y (a • c)=a • cone y c) ∧
    (∀ c d : Chain V, ∀ w : Finset V → ℤ, evaluate (c+d) w=evaluate c w+evaluate d w) ∧
    (∀ c d : Chain V, ∀ w : Finset V → ℤ, evaluate (c-d) w=evaluate c w-evaluate d w) ∧
    (∀ a : ℤ, ∀ c : Chain V, ∀ w : Finset V → ℤ, evaluate (a • c) w=a * evaluate c w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d; exact (BoundaryOperator (V := V)).map_add c d
  · intro c d; exact (BoundaryOperator (V := V)).map_sub c d
  · intro a c; exact (BoundaryOperator (V := V)).map_zsmul a c
  · intro y c d; exact (ConeOperator y).map_add c d
  · intro y c d; exact (ConeOperator y).map_sub c d
  · intro y a c; exact (ConeOperator y).map_zsmul a c
  · intro c d w; exact (PairingOperator w).map_add c d
  · intro c d w; exact (PairingOperator w).map_sub c d
  · intro a c w; exact (PairingOperator w).map_zsmul a c
end

section
noncomputable section
open scoped BigOperators
open PLDegree

private theorem PLDegree.boundary_pairing {V : Type*} [LinearOrder V]
    (c : Chain V) (w : Finset V → ℤ) :
    evaluate (boundary c) w = c.sum (fun s a => a * ∑ v ∈ s, incidence s v * w (s.erase v)) := by
  classical
  have hsingle (t : Finset V) (a : ℤ) :
      PairingOperator w (Finsupp.single t a) = a*w t := by
    exact Finsupp.sum_single_index (h := fun t a => a*w t) (zero_mul (w t))
  have hface (s : Finset V) : PairingOperator w (faceBoundary s) =
      ∑ v ∈ s, incidence s v*w (s.erase v) := by
    simp only [faceBoundary, map_sum, hsingle]
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    exact congrArg w (congrArg (fun d : DecidableEq V => @Finset.erase V d s v)
      (Subsingleton.elim _ _))
  change PairingOperator w (∑ s ∈ c.support, c s • faceBoundary s) = _
  rw [map_sum]
  simp only [map_sum, map_zsmul, hface, smul_eq_mul, Finsupp.sum]
end
end

section
open scoped BigOperators
open PLDegree

private theorem PLDegree.ray_formula_implies_cycle {V : Type*} [LinearOrder V]
    (c : Chain V) (j w : Finset V → ℤ) (hc : IsCycle c)
    (h : ∀ s ∈ c.support, j s= - ∑ v ∈ s, incidence s v*w (s.erase v)) :
    evaluate c j=0 := by
  have hsingle (t : Finset V) (a : ℤ) :
      PairingOperator w (Finsupp.single t a) = a*w t := by
    exact Finsupp.sum_single_index (h := fun t a => a*w t) (zero_mul (w t))
  have hface (s : Finset V) : PairingOperator w (faceBoundary s) =
      ∑ v ∈ s, incidence s v*w (s.erase v) := by
    simp only [faceBoundary, map_sum, hsingle]
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    exact congrArg w (congrArg (fun d : DecidableEq V => @Finset.erase V d s v)
      (Subsingleton.elim _ _))
  have hp : PairingOperator w (boundary c) =
      ∑ s ∈ c.support, c s * ∑ v ∈ s, incidence s v*w (s.erase v) := by
    change PairingOperator w (∑ s ∈ c.support, c s • faceBoundary s) = _
    simp only [map_sum, map_zsmul, hface, smul_eq_mul]
  have he : evaluate c j = -PairingOperator w (boundary c) := by
    rw [hp, evaluate, Finsupp.sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [h s hs, mul_neg]
  change boundary c=0 at hc
  rw [he, hc]
  simp
end

section
open scoped BigOperators
open PLDegree

private theorem PLDegree.cycle_degree_zero {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) (c : Chain V)
    (hc : IsCycle c) (hgp : ChainGP F c) : signedCount F c = 0 := by
  have hfamily : ∀ s ∈ c.support,
      s.card=n+1 ∧ augmentedDet F s ≠ 0 ∧ NoBoundaryZero F s := by
    intro s hs
    have h := hgp s hs
    exact ⟨h.1, h.2.1, PLDegree.simplex_gp_no_boundary_zero F s h⟩
  obtain ⟨u, hu⟩ := (PLDegree.simplex_ray_formula hn F).2 c.support hfamily
  have hformula : ∀ s ∈ c.support,
      simplexDegree F s= - ∑ v ∈ s, incidence s v*rayWeight F u (s.erase v) := by
    intro s hs
    have h := hfamily s hs
    exact ((PLDegree.simplex_ray_formula hn F).1 s h.1 h.2.1 h.2.2).2 u (hu s hs)
  exact PLDegree.ray_formula_implies_cycle c (simplexDegree F) (rayWeight F u) hc hformula
end

section

set_option autoImplicit false
open scoped BigOperators
open PLDegree
attribute [local instance] Classical.propDecidable

private theorem PLDegree.face_cone_boundary {V : Type*} [LinearOrder V]
    (y : V) (s : Finset V) (hy : y ∉ s) :
    boundary (faceCone y s) = Finsupp.single s 1 - cone y (faceBoundary s) := by
  classical
  have dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq V) =
      (LinearOrder.toDecidableEq : DecidableEq V) := Subsingleton.elim _ _
  have hsign (v : V) (hv : v ∈ s) :
      incidence (insert y s) y * incidence (insert y s) v =
        -(incidence s v * incidence (insert y (s.erase v)) y) := by
    have hself : rank (insert y s) y=rank s y := by simp [rank, Finset.filter_insert]
    have hself' : rank (insert y (s.erase v)) y=rank (s.erase v) y := by simp [rank, Finset.filter_insert]
    have hne : y ≠ v := fun h => hy (h ▸ hv)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hi : rank (insert y s) v=rank s v+1 := by simp [rank, Finset.filter_insert, hlt, hy]
      have he : rank (s.erase v) y=rank s y := by
        simp [rank, Finset.filter_erase, not_lt_of_ge (le_of_lt hlt)]
      simp only [incidence, hself, hself', hi, he, pow_succ]
      ring
    · have hi : rank (insert y s) v=rank s v := by
        simp [rank, Finset.filter_insert, not_lt_of_ge (le_of_lt hgt)]
      have hf : v ∈ s.filter (fun w => w<y) := Finset.mem_filter.mpr ⟨hv, hgt⟩
      have he : rank s y=rank (s.erase v) y+1 := by
        dsimp [rank]
        rw [Finset.filter_erase]
        convert (Finset.card_erase_add_one hf).symm using 1 <;> congr! <;> exact Subsingleton.elim _ _
      simp only [incidence, hself, hself', hi, he, pow_succ]
      ring
  have hsquare : incidence (insert y s) y * incidence (insert y s) y=1 := by
    simp [incidence, ← mul_pow]
  have hboundary (t : Finset V) (a : ℤ) :
      boundary (Finsupp.single t a)=a • faceBoundary t := by
    exact Finsupp.sum_single_index (h := fun t a => a • faceBoundary t) (zero_smul ℤ _)
  have hcone (t : Finset V) (a : ℤ) :
      ConeOperator y (Finsupp.single t a)=a • faceCone y t := by
    exact Finsupp.sum_single_index (h := fun t a => a • faceCone y t) (zero_smul ℤ _)
  have hcface : cone y (faceBoundary s)=
      ∑ v ∈ s, incidence s v • faceCone y (s.erase v) := by
    change ConeOperator y (faceBoundary s)=_
    simp only [faceBoundary, map_sum, hcone]
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    exact congrArg (faceCone y) (congrArg (fun d : DecidableEq V => @Finset.erase V d s v)
      (Subsingleton.elim _ _))
  rw [faceCone, if_neg hy, hboundary, faceBoundary]
  have hsum : (∑ v ∈ insert y s, Finsupp.single ((insert y s).erase v) (incidence (insert y s) v)) =
      Finsupp.single ((insert y s).erase y) (incidence (insert y s) y) +
      ∑ v ∈ s, Finsupp.single ((insert y s).erase v) (incidence (insert y s) v) := by
    convert Finset.sum_insert hy using 1 <;> congr! <;> exact Subsingleton.elim _ _
  try rw [dEq] at hsign
  try rw [dEq] at hsquare
  try rw [dEq] at hboundary
  try rw [dEq] at hcone
  try rw [dEq] at hcface
  try rw [dEq] at hsum
  rw [dEq]
  rw [hsum]
  rw [smul_add, Finset.smul_sum]
  have hfirst : incidence (insert y s) y •
      Finsupp.single ((insert y s).erase y) (incidence (insert y s) y)=Finsupp.single s 1 := by
    simp only [Finset.erase_insert hy, Finsupp.smul_single, smul_eq_mul, hsquare]
  rw [hfirst, hcface, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  have hne : y ≠ v := fun h => hy (h ▸ hv)
  have hyerase : y ∉ s.erase v := fun h => hy (Finset.mem_of_mem_erase h)
  have hset : (insert y s).erase v=insert y (s.erase v) := by
    ext w
    simp [Finset.mem_erase, Finset.mem_insert, hne]
    aesop
  simp only [hset, faceCone, if_neg hyerase, Finsupp.smul_single, smul_eq_mul]
  rw [← Finsupp.single_neg, hsign v hv]
  all_goals rw [dEq]

set_option autoImplicit false
open scoped BigOperators
open PLDegree

private theorem PLDegree.cone_boundary {V : Type*} [LinearOrder V]
    (y : V) (c : Chain V) (hy : Fresh y c) :
    boundary (cone y c)=c-cone y (boundary c) := by
  have hb : boundary (cone y c)=∑ s ∈ c.support, c s • boundary (faceCone y s) := by
    change BoundaryOperator (∑ s ∈ c.support, c s • faceCone y s)=_
    simp only [map_sum, map_zsmul]
    rfl
  have hc : cone y (boundary c)=∑ s ∈ c.support, c s • cone y (faceBoundary s) := by
    change ConeOperator y (∑ s ∈ c.support, c s • faceBoundary s)=_
    simp only [map_sum, map_zsmul]
    rfl
  have hr : (∑ s ∈ c.support, Finsupp.single s (c s))=c := by
    exact Finsupp.sum_single c
  calc
    boundary (cone y c) = ∑ s ∈ c.support, c s • boundary (faceCone y s) := hb
    _ = ∑ s ∈ c.support, c s • (Finsupp.single s 1-cone y (faceBoundary s)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [PLDegree.face_cone_boundary y s (hy s hs)]
    _ = (∑ s ∈ c.support, Finsupp.single s (c s)) -
        ∑ s ∈ c.support, c s • cone y (faceBoundary s) := by
      simp only [smul_sub, Finset.sum_sub_distrib, Finsupp.smul_single, smul_eq_mul, mul_one]
    _ = c-cone y (boundary c) := by rw [hr, ← hc]

set_option autoImplicit false
open scoped BigOperators
open PLDegree

set_option maxHeartbeats 600000
universe u

private theorem PLDegree.link_chain_algebra {V : Type u} [LinearOrder V] :
    (∀ y : V, ∀ c : Chain V, boundary (link y c) = -link y (boundary c)) ∧
    (∀ y : V, ∀ c : Chain V, Fresh y (link y c)) ∧
    (∀ y s : V, ∀ c : Chain V, Fresh s c → Fresh s (link y c)) ∧
    (∀ y s : V, ∀ c : Chain V, Fresh s c → s ≠ y → Fresh s (cone y c)) ∧
    (∀ s : V, ∀ c d : Chain V, Fresh s c → Fresh s d → Fresh s (c+d)) ∧
    (∀ s : V, ∀ c d : Chain V, Fresh s c → Fresh s d → Fresh s (c-d)) := by
  classical
  have dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq V) =
      (LinearOrder.toDecidableEq : DecidableEq V) := Subsingleton.elim _ _
  let L (y : V) : Chain V →+ Chain V := {
    toFun := link y
    map_zero' := by simp [link]
    map_add' := fun c d => Finsupp.sum_add_index'
      (fun t => by split_ifs <;> simp)
      (fun t a b => by split_ifs <;> simp [add_smul]) }
  have lval (y : V) (c : Chain V) : L y c = link y c := rfl
  have fresh_iff (s : V) (c : Chain V) :
      Fresh s c ↔ ∀ t : Finset V, s ∈ t → c t = 0 := by
    constructor
    · intro h t ht
      by_contra hn
      exact h t (Finsupp.mem_support_iff.mpr hn) ht
    · intro h t ht hst
      exact (Finsupp.mem_support_iff.mp ht) (h t hst)
  have fresh_zero (s : V) : Fresh s (0 : Chain V) := by simp [Fresh]
  have fresh_add (s : V) (c d : Chain V) (hc : Fresh s c) (hd : Fresh s d) :
      Fresh s (c+d) := by
    rw [fresh_iff] at hc hd ⊢
    intro t ht
    simp [hc t ht, hd t ht]
  have fresh_sub (s : V) (c d : Chain V) (hc : Fresh s c) (hd : Fresh s d) :
      Fresh s (c-d) := by
    rw [fresh_iff] at hc hd ⊢
    intro t ht
    simp [hc t ht, hd t ht]
  have fresh_smul (s : V) (a : ℤ) (c : Chain V) (hc : Fresh s c) :
      Fresh s (a • c) := by
    rw [fresh_iff] at hc ⊢
    intro t ht
    simp [hc t ht]
  have fresh_sum (s : V) {I : Type u} (f : I → Chain V) (A : Finset I)
      (hf : ∀ i ∈ A, Fresh s (f i)) : Fresh s (∑ i ∈ A, f i) := by
    rw [fresh_iff]
    intro t ht
    simp only [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    exact (fresh_iff s (f i)).mp (hf i hi) t ht
  have fresh_single (s : V) (t : Finset V) (a : ℤ) (hs : s ∉ t) :
      Fresh s (Finsupp.single t a) := by
    rw [fresh_iff]
    intro u hu
    have hne : t ≠ u := by intro he; exact hs (he ▸ hu)
    simp [Finsupp.single_apply, hne]
  have fresh_face_boundary (s : V) (t : Finset V) (hs : s ∉ t) :
      Fresh s (faceBoundary t) := by
    apply fresh_sum s _ t
    intro v hv
    apply fresh_single
    intro h
    simp only [Finset.mem_erase] at h
    exact hs h.2
  have fresh_boundary (s : V) (c : Chain V) (hc : Fresh s c) :
      Fresh s (boundary c) := by
    apply fresh_sum s _ c.support
    intro t ht
    exact fresh_smul s (c t) (faceBoundary t) (fresh_face_boundary s t (hc t ht))
  have fresh_link_self (y : V) (c : Chain V) : Fresh y (link y c) := by
    apply fresh_sum y _ c.support
    intro t ht
    by_cases hy : y ∈ t
    · simp only [if_pos hy]
      apply fresh_smul
      rw [dEq]
      exact fresh_single y (t.erase y) (incidence t y) (by simp)
    · simp only [if_neg hy]
      exact fresh_zero y
  have fresh_link (y s : V) (c : Chain V) (hs : Fresh s c) :
      Fresh s (link y c) := by
    apply fresh_sum s _ c.support
    intro t ht
    by_cases hy : y ∈ t
    · simp only [if_pos hy]
      apply fresh_smul
      apply fresh_single
      intro h
      simp only [Finset.mem_erase] at h
      exact hs t ht h.2
    · simp only [if_neg hy]
      exact fresh_zero s
  have fresh_cone (y s : V) (c : Chain V) (hs : Fresh s c) (hne : s ≠ y) :
      Fresh s (cone y c) := by
    apply fresh_sum s _ c.support
    intro t ht
    apply fresh_smul
    dsimp only [faceCone]
    split_ifs
    · exact fresh_zero s
    · apply fresh_single
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne, hs t ht⟩
  have lsingle (y : V) (t : Finset V) (a : ℤ) :
      L y (Finsupp.single t a) =
        if y ∈ t then a • Finsupp.single (t.erase y) (incidence t y) else 0 := by
    rw [lval, link]
    rw [dEq]
    exact Finsupp.sum_single_index (h := fun t a =>
      if y ∈ t then a • Finsupp.single (t.erase y) (incidence t y) else 0)
      (by split_ifs <;> simp)
  have lzero (y : V) (c : Chain V) (hc : Fresh y c) : L y c = 0 := by
    rw [lval, link]
    change (∑ t ∈ c.support, _) = 0
    apply Finset.sum_eq_zero
    intro t ht
    simp [hc t ht]
  have lface_cone (y : V) (t : Finset V) (hy : y ∉ t) :
      L y (faceCone y t) = Finsupp.single t 1 := by
    rw [faceCone, if_neg hy, lsingle]
    rw [dEq]
    simp only [Finset.mem_insert_self, if_true, Finset.erase_insert hy,
      Finsupp.smul_single, smul_eq_mul]
    have hsquare : incidence (insert y t) y * incidence (insert y t) y=1 := by
      simp [incidence, ← mul_pow]
    rw [hsquare]
  have lcone (y : V) (c : Chain V) (hy : Fresh y c) : L y (cone y c) = c := by
    change L y (∑ t ∈ c.support, c t • faceCone y t) = c
    simp only [map_sum, map_zsmul]
    calc
      (∑ t ∈ c.support, c t • L y (faceCone y t)) =
          ∑ t ∈ c.support, Finsupp.single t (c t) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [lface_cone y t (hy t ht)]
        simp
      _ = c := Finsupp.sum_single c
  have bsingle (t : Finset V) (a : ℤ) :
      boundary (Finsupp.single t a) = a • faceBoundary t := by
    exact Finsupp.sum_single_index (h := fun t a => a • faceBoundary t) (zero_smul ℤ _)
  have lface_boundary (y : V) (t : Finset V) :
      L y (faceBoundary t) = -boundary (L y (Finsupp.single t 1)) := by
    by_cases hy : y ∈ t
    · have hyer : y ∉ t.erase y := by simp
      have hbc := PLDegree.face_cone_boundary y (t.erase y) hyer
      rw [faceCone, if_neg hyer] at hbc
      rw [dEq] at hbc
      rw [Finset.insert_erase hy, bsingle] at hbc
      have hLb := congrArg (L y) hbc
      rw [map_zsmul, map_sub, lsingle, if_neg hyer,
        lcone y (faceBoundary (t.erase y)) (fresh_face_boundary y (t.erase y) hyer)] at hLb
      have hsq : incidence t y * incidence t y = 1 := by simp [incidence, ← mul_pow]
      have hLb2 := congrArg (fun c : Chain V => incidence t y • c) hLb
      simp only [smul_smul, hsq, one_smul, zero_sub, smul_neg] at hLb2
      rw [lsingle, if_pos hy, one_smul, bsingle]
      exact hLb2
    · rw [lzero y (faceBoundary t) (fresh_face_boundary y t hy), lsingle, if_neg hy]
      simp [boundary]
  have llinear (y : V) (c : Chain V) :
      L y c = ∑ t ∈ c.support, c t • L y (Finsupp.single t 1) := by
    rw [lval, link]
    change (∑ t ∈ c.support, _) = _
    apply Finset.sum_congr rfl
    intro t ht
    rw [lsingle]
    rw [dEq]
    split_ifs with h <;> simp [h]
  have anti (y : V) (c : Chain V) : boundary (link y c) = -link y (boundary c) := by
    rw [← lval y c, ← lval y (boundary c), llinear y c]
    change BoundaryOperator (∑ t ∈ c.support, c t • L y (Finsupp.single t 1)) =
      -L y (∑ t ∈ c.support, c t • faceBoundary t)
    simp only [map_sum, map_zsmul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    change c t • boundary (L y (Finsupp.single t 1)) = -(c t • L y (faceBoundary t))
    rw [lface_boundary y t]
    simp
  exact ⟨anti, fresh_link_self, fresh_link, fresh_cone, fresh_add, fresh_sub⟩

set_option autoImplicit false
open scoped BigOperators
open PLDegree

private theorem PLDegree.link_move_boundary {V : Type*} [LinearOrder V]
    (z : Chain V) (y y' : V) (hc : IsCycle z) (hy' : Fresh y' z) (hne : y' ≠ y) :
    IsCycle (link y z) ∧ IsCycle (moveVertex y y' z) ∧
    boundary (bubble y y' z)=z-moveVertex y y' z ∧
    ∀ s : V, Fresh s z → s ≠ y → s ≠ y' → Fresh s (moveVertex y y' z) := by
  rcases PLDegree.link_chain_algebra (V := V) with ⟨hanti, hself, hfl, hfc, hfa, hfs⟩
  have hlink : IsCycle (link y z) := by
    change boundary (link y z) = 0
    rw [hanti y z]
    change boundary z = 0 at hc
    rw [hc]
    simp [link]
  have hcy : boundary (cone y (link y z)) = link y z := by
    rw [PLDegree.cone_boundary y (link y z) (hself y z)]
    change boundary (link y z) = 0 at hlink
    rw [hlink]
    simp [cone]
  have hl' : Fresh y' (link y z) := hfl y y' z hy'
  have hcy' : boundary (cone y' (link y z)) = link y z := by
    rw [PLDegree.cone_boundary y' (link y z) hl']
    change boundary (link y z) = 0 at hlink
    rw [hlink]
    simp [cone]
  have hmove : IsCycle (moveVertex y y' z) := by
    change BoundaryOperator (z-cone y (link y z)+cone y' (link y z)) = 0
    rw [map_add, map_sub]
    change boundary z - boundary (cone y (link y z)) + boundary (cone y' (link y z)) = 0
    change boundary z = 0 at hc
    rw [hc, hcy, hcy']
    abel
  have hbub : boundary (bubble y y' z) = z-moveVertex y y' z := by
    rw [bubble, PLDegree.cone_boundary y' (cone y (link y z))
      (hfc y y' (link y z) hl' hne), hcy]
    dsimp only [moveVertex]
    abel
  have hfresh : ∀ s : V, Fresh s z → s ≠ y → s ≠ y' → Fresh s (moveVertex y y' z) := by
    intro s hs hsy hsy'
    apply hfa
    · exact hfs s z (cone y (link y z)) hs (hfc y s (link y z) (hfl y s z hs) hsy)
    · exact hfc y' s (link y z) (hfl y s z hs) hsy'
  exact ⟨hlink, hmove, hbub, hfresh⟩

end

section
open scoped BigOperators
open PLDegree

theorem proof_PLDegree_apex_independence {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) (z : Chain V) (s s' : V)
    (hz : Homogeneous n z) (hcycle : IsCycle z)
    (hs : Fresh s z) (hs' : Fresh s' z)
    (hg : ChainGP F (cone s z)) (hg' : ChainGP F (cone s' z)) :
    signedCount F (cone s z)=signedCount F (cone s' z) := by
  have hc : IsCycle (cone s z-cone s' z) := by
    change BoundaryOperator (cone s z-cone s' z)=0
    rw [map_sub]
    change boundary (cone s z)-boundary (cone s' z)=0
    rw [PLDegree.cone_boundary s z hs, PLDegree.cone_boundary s' z hs']
    change boundary z=0 at hcycle
    rw [hcycle]
    simp [cone]
  have hgp : ChainGP F (cone s z-cone s' z) := by
    intro t ht
    by_cases h : t ∈ (cone s z).support
    · exact hg t h
    · apply hg' t
      by_contra h'
      have hzero : (cone s z) t=0 := by
        by_contra hnz
        exact h (Finsupp.mem_support_iff.mpr hnz)
      have hzero' : (cone s' z) t=0 := by
        by_contra hnz
        exact h' (Finsupp.mem_support_iff.mpr hnz)
      have hnz := Finsupp.mem_support_iff.mp ht
      apply hnz
      simp only [Finsupp.sub_apply, hzero, hzero', sub_self]
  have hzero := PLDegree.cycle_degree_zero hn F (cone s z-cone s' z) hc hgp
  change PairingOperator (simplexDegree F) (cone s z-cone s' z)=0 at hzero
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero
end

