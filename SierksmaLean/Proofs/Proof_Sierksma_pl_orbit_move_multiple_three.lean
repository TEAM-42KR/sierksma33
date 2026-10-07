import SierksmaLean.Definitions.Def_PLDegree_Chain
import SierksmaLean.Definitions.Def_PLDegree_AffineRayHit
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import SierksmaLean.Definitions.Def_PLDegree_BoundaryOperator
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import Mathlib
import SierksmaLean.Definitions.Def_Sierksma_L6Old
section

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

theorem PLDegree.vertex_move_bubble {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) (z : Chain V) (y y' s : V)
    (hz : Homogeneous n z) (hc : IsCycle z)
    (hy' : Fresh y' z) (hne : y' ≠ y) (hs : Fresh s z) (hsy : s ≠ y) (hsy' : s ≠ y')
    (hg : ChainGP F (cone s z)) (hg' : ChainGP F (cone s (moveVertex y y' z)))
    (hgb : ChainGP F (bubble y y' z)) :
    IsCycle (link y z) ∧
      signedCount F (cone s z)-signedCount F (cone s (moveVertex y y' z)) =
        signedCount F (bubble y y' z) := by
  obtain ⟨hell, hm, hb, hsm⟩ := PLDegree.link_move_boundary z y y' hc hy' hne
  refine ⟨hell, ?_⟩
  have hcy : IsCycle (cone s z-cone s (moveVertex y y' z)-bubble y y' z) := by
    change BoundaryOperator (cone s z-cone s (moveVertex y y' z)-bubble y y' z)=0
    simp only [map_sub]
    change boundary (cone s z)-boundary (cone s (moveVertex y y' z))-
      boundary (bubble y y' z)=0
    rw [PLDegree.cone_boundary s z hs,
      PLDegree.cone_boundary s (moveVertex y y' z) (hsm s hs hsy hsy'), hb]
    change boundary z=0 at hc
    change boundary (moveVertex y y' z)=0 at hm
    rw [hc, hm]
    simp [cone]
  have hgp : ChainGP F (cone s z-cone s (moveVertex y y' z)-bubble y y' z) := by
    intro t ht
    by_cases h1 : t ∈ (cone s z).support
    · exact hg t h1
    by_cases h2 : t ∈ (cone s (moveVertex y y' z)).support
    · exact hg' t h2
    apply hgb t
    by_contra h3
    have hz1 : (cone s z) t=0 := by
      by_contra ha; exact h1 (Finsupp.mem_support_iff.mpr ha)
    have hz2 : (cone s (moveVertex y y' z)) t=0 := by
      by_contra ha; exact h2 (Finsupp.mem_support_iff.mpr ha)
    have hz3 : (bubble y y' z) t=0 := by
      by_contra ha; exact h3 (Finsupp.mem_support_iff.mpr ha)
    have hnz := Finsupp.mem_support_iff.mp ht
    apply hnz
    simp only [Finsupp.sub_apply, hz1, hz2, hz3, sub_self]
  have hzero := PLDegree.cycle_degree_zero hn F
    (cone s z-cone s (moveVertex y y' z)-bubble y y' z) hcy hgp
  change PairingOperator (simplexDegree F)
    (cone s z-cone s (moveVertex y y' z)-bubble y y' z)=0 at hzero
  simp only [map_sub] at hzero
  exact sub_eq_zero.mp hzero
end

end

section
section
open scoped BigOperators
open PLDegree

private theorem PLDegree.apex_independence {V : Type*} [LinearOrder V] {n : ℕ}
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

end

section
open PLDegree
open scoped BigOperators
set_option maxHeartbeats 800000

private theorem l6closed_2_listSign_cons_local {V : Type*} [LinearOrder V] {k : ℕ} (y : V) (t : Fin k → V) :
    listSign (Fin.cons y t)=(-1)^((Finset.univ.filter (fun i => t i < y)).card)*listSign t := by
  classical
  have hsucc (x : Fin k) : 0 < x.succ := by
    change 0 < x.val+1
    omega
  unfold listSign
  rw [← pow_add]
  congr 1
  simp only [Finset.card_filter]
  rw [← Finset.univ_product_univ,Finset.sum_product]
  rw [← Finset.univ_product_univ,Finset.sum_product]
  simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hsucc,
    Fin.not_lt_zero,Fin.succ_lt_succ_iff,true_and,false_and,ite_false]
  simp only [add_zero,zero_add]
  congr 2 <;> simp_all
  funext x
  simp only [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x < i ∧ t i < t x <;> simp [h]

theorem PLDegree.cone_listed_face {V : Type*} [LinearOrder V] {k : ℕ}
    (y : V) (t : Fin k → V) (ht : Function.Injective t) (hy : ∀ i, t i ≠ y) :
    cone y (listedFace t)=listedFace (Fin.cons y t) := by
  classical
  let S := Finset.univ.image t
  have hsingle : listedFace t=Finsupp.single S (listSign t) := by
    unfold listedFace
    congr 1 <;> ext v <;> simp [S]
  have hyS : y∉S := by
    simp only [S,Finset.mem_image,Finset.mem_univ,true_and,not_exists]
    exact hy
  have himage : Finset.univ.image (Fin.cons y t)=insert y S := by
    ext v
    simp [S,Fin.exists_fin_succ,eq_comm]
  have hfilter : (insert y S).filter (fun v => v<y) =
      (Finset.univ.filter (fun i => t i<y)).image t := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_insert,S,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨hmem,hlt⟩
      rcases hmem with rfl | ⟨i,rfl⟩
      · exact (lt_irrefl _ hlt).elim
      · exact ⟨i,hlt,rfl⟩
    · rintro ⟨i,hlt,rfl⟩
      exact ⟨Or.inr ⟨i,rfl⟩,hlt⟩
  have hrank : rank (insert y S) y=(Finset.univ.filter (fun i => t i<y)).card := by
    unfold rank
    calc
      _ = ((Finset.univ.filter (fun i => t i<y)).image t).card := by
        apply congrArg Finset.card
        apply Finset.ext
        intro v
        simpa only [Finset.mem_filter,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] using Finset.ext_iff.mp hfilter v
      _ = _ := Finset.card_image_of_injective _ ht
  rw [hsingle]
  unfold cone
  rw [Finsupp.sum_single_index (by simp)]
  unfold faceCone
  rw [if_neg hyS]
  unfold listedFace
  rw [l6closed_2_listSign_cons_local]
  simp only [Finsupp.smul_single,smul_eq_mul,incidence,hrank]
  congr 1
  · apply Finset.ext
    intro v
    simpa only [Finset.mem_image,Finset.mem_insert,Finset.mem_univ,true_and] using (Finset.ext_iff.mp himage v).symm
  · ring_nf
    apply congrArg (fun n : ℕ => listSign t * (-1)^n)
    unfold rank
    calc
      _ = ((Finset.univ.filter (fun i => t i<y)).image t).card := by
        apply congrArg Finset.card
        apply Finset.ext
        intro v
        simpa only [Finset.mem_filter,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] using Finset.ext_iff.mp hfilter v
      _ = _ := Finset.card_image_of_injective _ ht
end

section
open PLDegree
open scoped BigOperators
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

private theorem l6closed_3_listSign_comp_perm_local {V : Type*} [LinearOrder V] {k : ℕ}
    (t : Fin k → V) (ht : Function.Injective t) (p : Equiv.Perm (Fin k)) :
    listSign (t ∘ p)=(p.sign : ℤ)*listSign t := by
  classical
  have hsign : ∀ {k : ℕ} (p : Equiv.Perm (Fin k)) (t : Fin k → V),
      StrictMono t → listSign (t ∘ p) = (p.sign : ℤ) := by
    intro k p t ht
    unfold listSign
    simp only [Function.comp_apply, ht.lt_iff_lt]
    rw [p.sign_eq_prod_prod_Ioi]
    simp only [Units.coe_prod]
    rw [← Finset.prod_const, Finset.prod_filter]
    rw [← Finset.univ_product_univ, Finset.prod_product]
    apply Finset.prod_congr rfl
    intro i hi
    rw [show Finset.Ioi i = Finset.univ.filter (fun j => i < j) by ext; simp,
      Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hij : i < j
    · have hne : p i ≠ p j := p.injective.ne hij.ne
      rcases lt_or_gt_of_ne hne with hp | hp <;> simp [hij, hp, hp.not_gt]
    · simp [hij]
  let S := Finset.univ.image t
  have hcard : S.card=k := by simpa [S] using Finset.card_image_of_injective Finset.univ ht
  let e : Fin k → Fin k := fun i =>
    (S.orderIsoOfFin hcard).symm ⟨t i,Finset.mem_image_of_mem t (Finset.mem_univ i)⟩
  have he : Function.Injective e := by
    intro i j hij
    have hh := congrArg (fun z => ((S.orderIsoOfFin hcard z : S) : V)) hij
    have hv : t i=t j := by simpa [e] using hh
    exact ht hv
  let q : Equiv.Perm (Fin k) := Equiv.ofBijective e ⟨he,Finite.injective_iff_surjective.mp he⟩
  have hq : S.orderEmbOfFin hcard ∘ q=t := by
    funext i
    change (((S.orderIsoOfFin hcard) (e i) : S) : V)=t i
    simp [e]
  have htSign : listSign t=(q.sign : ℤ) := by
    rw [← hq]
    exact hsign q (S.orderEmbOfFin hcard) (S.orderEmbOfFin hcard).strictMono
  have hqp : listSign (t ∘ p)=((q*p).sign : ℤ) := by
    have heq : t ∘ p=S.orderEmbOfFin hcard ∘ (q*p) := by
      rw [← hq]
      rfl
    rw [heq]
    exact hsign (q*p) (S.orderEmbOfFin hcard) (S.orderEmbOfFin hcard).strictMono
  rw [hqp,htSign,map_mul,Units.val_mul]
  exact mul_comm _ _

theorem PLDegree.relabel_listed_face {V : Type*} [LinearOrder V] {k : ℕ}
    (t : Fin k → V) (ht : Function.Injective t) (f : V → V) (hf : Function.Injective f) :
    relabel f (listedFace t)=listedFace (f ∘ t) := by
  classical
  let S := Finset.univ.image t
  have hcard : S.card=k := by simpa [S] using Finset.card_image_of_injective Finset.univ ht
  let e : Fin k → Fin k := fun i =>
    (S.orderIsoOfFin hcard).symm ⟨t i,Finset.mem_image_of_mem t (Finset.mem_univ i)⟩
  have he : Function.Injective e := by
    intro i j hij
    have hh := congrArg (fun z => ((S.orderIsoOfFin hcard z : S) : V)) hij
    have hv : t i=t j := by simpa [e] using hh
    exact ht hv
  let q : Equiv.Perm (Fin k) := Equiv.ofBijective e ⟨he,Finite.injective_iff_surjective.mp he⟩
  have hq : S.orderEmbOfFin hcard ∘ q=t := by
    funext i
    change (((S.orderIsoOfFin hcard) (e i) : S) : V)=t i
    simp [e]
  have hsorted : listSign (S.orderEmbOfFin hcard)=1 := by
    have hno (ij : Fin k × Fin k) : ¬(ij.1 < ij.2 ∧ ij.2 < ij.1) := by omega
    simp [listSign,(S.orderEmbOfFin hcard).strictMono.lt_iff_lt,hno]
  have htsign : listSign t=(q.sign : ℤ) := by
    rw [← hq,l6closed_3_listSign_comp_perm_local _ (S.orderEmbOfFin hcard).injective q,hsorted,mul_one]
  have hftsign : listSign (f ∘ t)=(q.sign : ℤ)*listSign (f ∘ S.orderEmbOfFin hcard) := by
    rw [← hq,← Function.comp_assoc]
    exact l6closed_3_listSign_comp_perm_local _ (hf.comp (S.orderEmbOfFin hcard).injective) q
  have hcast : ∀ {a b : ℕ} (h : a=b) (g : Fin b → V), listedFace (g ∘ Fin.cast h)=listedFace g := by
    intro a b h g
    subst b
    rfl
  have hlist : (fun i : Fin S.card => f (S.orderEmbOfFin rfl i)) =
      (f ∘ S.orderEmbOfFin hcard) ∘ Fin.cast hcard := by
    funext i
    apply congrArg f
    exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  have himage : Finset.univ.image (f ∘ S.orderEmbOfFin hcard)=Finset.univ.image (f ∘ t) := by
    rw [← Finset.image_image,Finset.image_orderEmbOfFin_univ]
    rw [← Finset.image_image]
  have hsingle : listedFace t=Finsupp.single S (listSign t) := by
    unfold listedFace
    congr 1 <;> ext v <;> simp [S]
  rw [hsingle]
  unfold relabel
  rw [Finsupp.sum_single_index (by simp)]
  change listSign t • listedFace (fun i : Fin S.card => f (S.orderEmbOfFin rfl i)) =
    listedFace (f ∘ t)
  rw [hlist,hcast]
  simp only [listedFace,Finsupp.smul_single,smul_eq_mul,himage,htsign,hftsign]
  congr 1
  apply Finset.ext
  intro v
  simpa only [Finset.mem_image,Finset.mem_univ,true_and] using Finset.ext_iff.mp himage v
end

section
open scoped BigOperators
open PLDegree Sierksma
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

private def l6closed_4_signC {k : ℕ} (t : Fin k → ℕ) : ℤ :=
  (-1) ^ ((Finset.univ.filter (fun ij : Fin k × Fin k => ij.1 < ij.2 ∧ t ij.2 < t ij.1)).card)
private def l6closed_4_rankC (s : Finset ℕ) (v : ℕ) : ℕ := (s.filter (fun w => w < v)).card
private def l6closed_4_face (a : Fin 4 → Fin 6) : Finset ℕ := Finset.univ.image (HexTuple a)

private theorem l6closed_4_signC_eq {k : ℕ} (t : Fin k → ℕ) : listSign t = l6closed_4_signC t := by
  unfold listSign l6closed_4_signC
  congr 2
  ext ij
  simp only [Finset.mem_filter]
private theorem l6closed_4_rankC_eq (s : Finset ℕ) (v : ℕ) : rank s v = l6closed_4_rankC s v := by
  unfold rank l6closed_4_rankC
  congr 1
  ext w
  simp only [Finset.mem_filter]

private theorem l6closed_4_listed_eq {k : ℕ} (t : Fin k → ℕ) :
    listedFace t = Finsupp.single (Finset.univ.image t) (l6closed_4_signC t) := by
  unfold listedFace
  congr 1
  · ext v
    simp only [Finset.mem_image]
  · exact l6closed_4_signC_eq t

private theorem l6closed_4_inj (a : Fin 4 → Fin 6) : Function.Injective (HexTuple a) := by
  intro k l h
  have hk := k.isLt
  have hl := l.isLt
  have ha : ∀ i, (a i).val < 6 := fun i => (a i).isLt
  have hm1 := ha ⟨k.val/2, by omega⟩
  have hm2 := ha ⟨l.val/2, by omega⟩
  have hn1 := Nat.mod_lt ((a ⟨k.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hn2 := Nat.mod_lt ((a ⟨l.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hg : k.val / 2 = l.val / 2 := by
    simp only [HexTuple] at h
    split_ifs at h <;> omega
  have he : (⟨k.val/2, by omega⟩ : Fin 4) = ⟨l.val/2, by omega⟩ := Fin.ext hg
  simp only [HexTuple, he, hg] at h
  apply Fin.ext
  split_ifs at h <;> omega

private theorem l6closed_4_face_card (a : Fin 4 → Fin 6) : (l6closed_4_face a).card=8 := by
  rw [l6closed_4_face, Finset.card_image_of_injective _ (l6closed_4_inj a)]
  decide

private def l6closed_4_boundaryHom : Chain ℕ →+ Chain ℕ where
  toFun c := boundary c
  map_zero' := by simp [boundary]
  map_add' c d := Finsupp.sum_add_index' (fun s => zero_smul ℤ (faceBoundary s))
    (fun s a b => add_smul a b (faceBoundary s))

private theorem l6closed_4_facet_boundary (a : Fin 4 → Fin 6) :
    boundary (listedFace (HexTuple a)) =
      ∑ k : Fin 8, Finsupp.single ((l6closed_4_face a).erase (HexTuple a k))
        (l6closed_4_signC (HexTuple a) * (-1)^l6closed_4_rankC (l6closed_4_face a) (HexTuple a k)) := by
  rw [l6closed_4_listed_eq, boundary, Finsupp.sum_single_index (by simp)]
  rw [faceBoundary, Finset.smul_sum]
  rw [Finset.sum_image (l6closed_4_inj a).injOn]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finsupp.smul_single, smul_eq_mul, incidence, l6closed_4_rankC_eq]
  congr 1
  ext v
  simp only [Finset.mem_erase, l6closed_4_face]

private theorem l6closed_4_support_face (s : Finset ℕ) (hs : s ∈ HexCycle.support) :
    ∃ a : Fin 4 → Fin 6, s = l6closed_4_face a := by
  by_contra hn
  apply (Finsupp.mem_support_iff.mp hs)
  rw [HexCycle, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [l6closed_4_listed_eq, Finsupp.single_apply, if_neg]
  intro he
  exact hn ⟨a, he.symm⟩

private theorem l6closed_4_homogeneous : Homogeneous 8 HexCycle := by
  intro s hs
  obtain ⟨a, rfl⟩ := l6closed_4_support_face s hs
  exact l6closed_4_face_card a

private theorem l6closed_4_orbit_arith (a : Fin 4 → Fin 6) (k l : Fin 8) :
    HexTuple a k < 24 ∧ ShiftVertex (HexTuple a k) ≠ HexTuple a l ∧
       ShiftVertex (ShiftVertex (HexTuple a k)) ≠ HexTuple a l := by
  have hk := k.isLt
  have hl := l.isLt
  have ha : ∀ i, (a i).val < 6 := fun i => (a i).isLt
  have hm1 := ha ⟨k.val/2, by omega⟩
  have hm2 := ha ⟨l.val/2, by omega⟩
  have hn1 := Nat.mod_lt ((a ⟨k.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hn2 := Nat.mod_lt ((a ⟨l.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hbound : HexTuple a k < 24 := by
    dsimp [HexTuple]
    split_ifs <;> omega
  refine ⟨hbound, ?_, ?_⟩
  all_goals
    intro heq
    have hblock : k.val/2 = l.val/2 := by
      simp only [ShiftVertex, if_pos hbound, HexTuple] at heq
      split_ifs at heq <;> omega
    have hf : (⟨k.val/2, by omega⟩ : Fin 4) = ⟨l.val/2, by omega⟩ := Fin.ext hblock
    simp only [ShiftVertex, if_pos hbound, HexTuple, hf, hblock] at heq
    split_ifs at heq <;> omega

private theorem l6closed_4_orbit_support : ∀ s ∈ HexCycle.support, ∀ v ∈ s,
    v<24 ∧ ShiftVertex v ∉ s ∧ ShiftVertex (ShiftVertex v) ∉ s := by
  intro s hs v hv
  obtain ⟨a, rfl⟩ := l6closed_4_support_face s hs
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨(l6closed_4_orbit_arith a k k).1, ?_, ?_⟩
  · intro h
    obtain ⟨l, _, heq⟩ := Finset.mem_image.mp h
    exact (l6closed_4_orbit_arith a k l).2.1 heq.symm
  · intro h
    obtain ⟨l, _, heq⟩ := Finset.mem_image.mp h
    exact (l6closed_4_orbit_arith a k l).2.2 heq.symm
private def l6closed_4_bt (b : Fin 4 → Fin 2 → Fin 6) (k : Fin 8) : ℕ :=
  6*(k.val/2)+(b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).val
private theorem l6closed_4_inversion (b : Fin 4 → Fin 2 → Fin 6) (k l : Fin 8) :
    (k < l ∧ l6closed_4_bt b l < l6closed_4_bt b k) ↔
      (k.val%2=0 ∧ l.val=k.val+1 ∧
       b ⟨k.val/2, by omega⟩ 1 < b ⟨k.val/2, by omega⟩ 0) := by
  have hk := k.isLt
  have hl := l.isLt
  have hbk := (b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).isLt
  have hbl := (b ⟨l.val/2, by omega⟩ ⟨l.val%2, by omega⟩).isLt
  constructor
  · intro ⟨h1,h2⟩
    have hi : k.val/2=l.val/2 := by dsimp [l6closed_4_bt] at h2; omega
    have hp : k.val%2=0 ∧ l.val%2=1 ∧ l.val=k.val+1 := by omega
    refine ⟨hp.1,hp.2.2,?_⟩
    have he : (⟨l.val/2, by omega⟩ : Fin 4)=⟨k.val/2, by omega⟩ := Fin.ext hi.symm
    have ke : (⟨k.val%2, by omega⟩ : Fin 2)=0 := Fin.ext hp.1
    have le : (⟨l.val%2, by omega⟩ : Fin 2)=1 := Fin.ext hp.2.1
    dsimp [l6closed_4_bt] at h2
    rw [he,ke,le] at h2
    omega
  · intro ⟨hp,he,l6closed_4_hb⟩
    have hi : k.val/2=l.val/2 := by omega
    have hlp : l.val%2=1 := by omega
    have hfi : (⟨l.val/2, by omega⟩ : Fin 4)=⟨k.val/2, by omega⟩ := Fin.ext hi.symm
    have ke : (⟨k.val%2, by omega⟩ : Fin 2)=0 := Fin.ext hp
    have le : (⟨l.val%2, by omega⟩ : Fin 2)=1 := Fin.ext hlp
    refine ⟨by omega,?_⟩
    dsimp [l6closed_4_bt]
    rw [hfi,ke,le]
    omega
private theorem l6closed_4_sign_block (b : Fin 4 → Fin 2 → Fin 6) :
    l6closed_4_signC (l6closed_4_bt b) = ∏ i : Fin 4, (if b i 1 < b i 0 then (-1:ℤ) else 1) := by
  have hc : (Finset.univ.filter (fun ij : Fin 8 × Fin 8 =>
      ij.1 < ij.2 ∧ l6closed_4_bt b ij.2 < l6closed_4_bt b ij.1)).card =
      ∑ i : Fin 4, if b i 1 < b i 0 then 1 else 0 := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [l6closed_4_inversion]
    rw [Fintype.sum_prod_type]
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    simp only [and_false, and_true, false_and, true_and, ite_false, ite_true,
      add_zero, zero_add]
    rfl
  unfold l6closed_4_signC
  rw [hc]
  simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, pow_add]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, pow_zero, mul_one]
  split_ifs <;> norm_num

private def l6closed_4_step (v : Fin 6) : Fin 6 := ⟨(v.val+1)%6, Nat.mod_lt _ (by omega)⟩
private def l6closed_4_hb (a : Fin 4 → Fin 6) (i : Fin 4) (j : Fin 2) : Fin 6 :=
  if j=0 then a i else l6closed_4_step (a i)
private theorem l6closed_4_hex_bt (a : Fin 4 → Fin 6) : HexTuple a = l6closed_4_bt (l6closed_4_hb a) := by
  funext k
  dsimp [HexTuple, l6closed_4_bt, l6closed_4_hb, l6closed_4_step]
  simp only [Fin.mk_eq_zero]
  split_ifs <;> rfl
private theorem l6closed_4_step_lt (v : Fin 6) : l6closed_4_step v < v ↔ v=5 := by
  have h := v.isLt
  simp only [l6closed_4_step, Fin.lt_def, Fin.ext_iff]
  omega
private theorem l6closed_4_sign_hex (a : Fin 4 → Fin 6) :
    l6closed_4_signC (HexTuple a) = ∏ i : Fin 4, if a i=5 then (-1:ℤ) else 1 := by
  rw [l6closed_4_hex_bt, l6closed_4_sign_block]
  apply Finset.prod_congr rfl
  intro i _
  simp only [l6closed_4_hb, Fin.reduceEq, ite_false, ite_true, l6closed_4_step_lt]
private theorem l6closed_4_block_less (b : Fin 4 → Fin 2 → Fin 6) (l k : Fin 8) :
    l6closed_4_bt b l < l6closed_4_bt b k ↔
      (l.val/2 < k.val/2 ∨ l.val/2=k.val/2 ∧
       b ⟨l.val/2, by omega⟩ ⟨l.val%2, by omega⟩ <
         b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩) := by
  have h1 := (b ⟨l.val/2, by omega⟩ ⟨l.val%2, by omega⟩).isLt
  have h2 := (b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).isLt
  simp only [l6closed_4_bt, Fin.lt_def]
  omega
private def l6closed_4_low (i : Fin 4) : Fin 8 := ⟨2*i.val, by omega⟩
private def l6closed_4_high (i : Fin 4) : Fin 8 := ⟨2*i.val+1, by omega⟩
private theorem l6closed_4_rank_as_sum (a : Fin 4 → Fin 6) (k : Fin 8) :
    l6closed_4_rankC (l6closed_4_face a) (HexTuple a k) =
      ∑ l : Fin 8, if HexTuple a l < HexTuple a k then 1 else 0 := by
  unfold l6closed_4_rankC l6closed_4_face
  rw [Finset.filter_image, Finset.card_image_of_injective _ (l6closed_4_inj a)]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
private theorem l6closed_4_rank_low (a : Fin 4 → Fin 6) (i : Fin 4) :
    l6closed_4_rankC (l6closed_4_face a) (HexTuple a (l6closed_4_low i)) = 2*i.val + if a i=5 then 1 else 0 := by
  rw [l6closed_4_rank_as_sum]
  simp_rw [l6closed_4_hex_bt, l6closed_4_block_less]
  fin_cases i <;>
    norm_num only [l6closed_4_low, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, l6closed_4_hb,
      Fin.mk_eq_zero, Fin.reduceEq, true_or, false_or, true_and, false_and,
      and_true, and_false, ite_true, ite_false, add_zero, zero_add]
  all_goals simp only [l6closed_4_step_lt, lt_self_iff_false, ite_false, add_zero, zero_add]
  all_goals omega
private theorem l6closed_4_step_gt (v : Fin 6) : v < l6closed_4_step v ↔ v≠5 := by
  have h := v.isLt
  simp only [l6closed_4_step, Fin.lt_def, Fin.ext_iff]
  omega
private theorem l6closed_4_rank_high (a : Fin 4 → Fin 6) (i : Fin 4) :
    l6closed_4_rankC (l6closed_4_face a) (HexTuple a (l6closed_4_high i)) = 2*i.val + if a i=5 then 0 else 1 := by
  rw [l6closed_4_rank_as_sum]
  simp_rw [l6closed_4_hex_bt, l6closed_4_block_less]
  fin_cases i <;>
    norm_num only [l6closed_4_high, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, l6closed_4_hb,
      Fin.mk_eq_zero, Fin.reduceEq, true_or, false_or, true_and, false_and,
      and_true, and_false, ite_true, ite_false, add_zero, zero_add]
  all_goals simp only [l6closed_4_step_gt, lt_self_iff_false, ite_false, add_zero, zero_add]
  all_goals split_ifs <;> omega

private def l6closed_4_eps (v : Fin 6) : ℤ := if v=5 then -1 else 1
private def l6closed_4_except (a : Fin 4 → Fin 6) (i : Fin 4) : ℤ :=
  ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, l6closed_4_eps (a j)
private def l6closed_4_coef (a : Fin 4 → Fin 6) (k : Fin 8) : ℤ :=
  l6closed_4_signC (HexTuple a) * (-1)^l6closed_4_rankC (l6closed_4_face a) (HexTuple a k)
private theorem l6closed_4_coef_low (a : Fin 4 → Fin 6) (i : Fin 4) :
    l6closed_4_coef a (l6closed_4_low i) = l6closed_4_except a i := by
  unfold l6closed_4_coef
  rw [l6closed_4_sign_hex, l6closed_4_rank_low, pow_add, pow_mul]
  norm_num
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  by_cases h : a i=5 <;> simp [l6closed_4_eps, l6closed_4_except, h]
private theorem l6closed_4_coef_high (a : Fin 4 → Fin 6) (i : Fin 4) :
    l6closed_4_coef a (l6closed_4_high i) = -l6closed_4_except a i := by
  unfold l6closed_4_coef
  rw [l6closed_4_sign_hex, l6closed_4_rank_high, pow_add, pow_mul]
  norm_num
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  by_cases h : a i=5 <;> simp [l6closed_4_eps, l6closed_4_except, h]
private def l6closed_4_stepE : Fin 6 ≃ Fin 6 where
  toFun := l6closed_4_step
  invFun v := ⟨(v.val+5)%6, Nat.mod_lt _ (by omega)⟩
  left_inv v := by apply Fin.ext; have h := v.isLt; dsimp [l6closed_4_step]; omega
  right_inv v := by apply Fin.ext; have h := v.isLt; dsimp [l6closed_4_step]; omega
private def l6closed_4_rotateAt (i : Fin 4) : (Fin 4 → Fin 6) ≃ (Fin 4 → Fin 6) :=
  Equiv.piCongrRight (fun j => if j=i then l6closed_4_stepE else Equiv.refl (Fin 6))
private theorem l6closed_4_rotate_apply (i j : Fin 4) (a : Fin 4 → Fin 6) :
    l6closed_4_rotateAt i a j = if j=i then l6closed_4_step (a j) else a j := by
  simp [l6closed_4_rotateAt, Equiv.piCongrRight_apply]
  split_ifs <;> rfl
private theorem l6closed_4_except_rotate (a : Fin 4 → Fin 6) (i : Fin 4) :
    l6closed_4_except (l6closed_4_rotateAt i a) i = l6closed_4_except a i := by
  unfold l6closed_4_except
  apply Finset.prod_congr rfl
  intro j hj
  rw [l6closed_4_rotate_apply, if_neg (Finset.mem_erase.mp hj).1]
private theorem l6closed_4_low_high_ne (i : Fin 4) : l6closed_4_low i ≠ l6closed_4_high i := by
  intro h
  have hv := congrArg Fin.val h
  change 2*i.val=2*i.val+1 at hv
  omega
private theorem l6closed_4_rotate_tuple (a : Fin 4 → Fin 6) (i : Fin 4) (k : Fin 8)
    (hk : k≠l6closed_4_high i) :
    HexTuple (l6closed_4_rotateAt i a) k = HexTuple a (Equiv.swap (l6closed_4_low i) (l6closed_4_high i) k) := by
  fin_cases i <;> fin_cases k
  all_goals simp_all [HexTuple,l6closed_4_rotate_apply,Equiv.swap_apply_def,l6closed_4_high,l6closed_4_low,l6closed_4_step]
private theorem l6closed_4_erase_pair (a : Fin 4 → Fin 6) (i : Fin 4) :
    (l6closed_4_face a).erase (HexTuple a (l6closed_4_low i)) =
      (l6closed_4_face (l6closed_4_rotateAt i a)).erase (HexTuple (l6closed_4_rotateAt i a) (l6closed_4_high i)) := by
  unfold l6closed_4_face
  rw [← Finset.image_erase (l6closed_4_inj a), ← Finset.image_erase (l6closed_4_inj (l6closed_4_rotateAt i a))]
  symm
  calc
    _ = ((Finset.univ.erase (l6closed_4_high i)).image (Equiv.swap (l6closed_4_low i) (l6closed_4_high i))).image
        (HexTuple a) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro k hk
      exact l6closed_4_rotate_tuple a i k (Finset.mem_erase.mp hk).1
    _ = _ := by
      rw [Finset.image_erase (Equiv.swap (l6closed_4_low i) (l6closed_4_high i)).injective,
        Finset.image_univ_of_surjective (Equiv.swap (l6closed_4_low i) (l6closed_4_high i)).surjective,
        Equiv.swap_apply_right]
private def l6closed_4_term (a : Fin 4 → Fin 6) (k : Fin 8) : Chain ℕ :=
  Finsupp.single ((l6closed_4_face a).erase (HexTuple a k)) (l6closed_4_coef a k)
private theorem l6closed_4_pair_term (a : Fin 4 → Fin 6) (i : Fin 4) :
    l6closed_4_term a (l6closed_4_low i) = -l6closed_4_term (l6closed_4_rotateAt i a) (l6closed_4_high i) := by
  unfold l6closed_4_term
  rw [l6closed_4_coef_low,l6closed_4_coef_high,l6closed_4_except_rotate,l6closed_4_erase_pair]
  simp
private theorem l6closed_4_sum_split (f : Fin 8 → Chain ℕ) :
    (∑ k, f k) = ∑ i : Fin 4, (f (l6closed_4_low i)+f (l6closed_4_high i)) := by
  simp [Fin.sum_univ_succ,l6closed_4_low,l6closed_4_high]
  abel
private theorem l6closed_4_cycle : IsCycle HexCycle := by
  change l6closed_4_boundaryHom HexCycle=0
  rw [HexCycle, map_sum]
  change (∑ a : Fin 4 → Fin 6, boundary (listedFace (HexTuple a)))=0
  simp_rw [l6closed_4_facet_boundary]
  change (∑ a : Fin 4 → Fin 6, ∑ k : Fin 8, l6closed_4_term a k)=0
  simp_rw [l6closed_4_sum_split]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_add_distrib]
  have hr : (∑ a : Fin 4 → Fin 6, l6closed_4_term a (l6closed_4_low i)) =
      -∑ a : Fin 4 → Fin 6, l6closed_4_term a (l6closed_4_high i) := by
    rw [← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv (l6closed_4_rotateAt i) _ _ (fun a => l6closed_4_pair_term a i)
  rw [hr]
  exact neg_add_cancel _

private def l6closed_4_sb (a : Fin 4 → Fin 6) (i : Fin 4) (j : Fin 2) : Fin 6 :=
  if a i=5 then (if j=0 then 0 else 5) else l6closed_4_hb a i j
private def l6closed_4_sortedTuple (a : Fin 4 → Fin 6) : Fin 8 → ℕ := l6closed_4_bt (l6closed_4_sb a)
private theorem l6closed_4_sb_increasing (a : Fin 4 → Fin 6) (i : Fin 4) : l6closed_4_sb a i 0 < l6closed_4_sb a i 1 := by
  by_cases h : a i=5
  · simp [l6closed_4_sb,h]
  · simp [l6closed_4_sb,h,l6closed_4_hb,l6closed_4_step_gt]
private theorem l6closed_4_sorted_strict (a : Fin 4 → Fin 6) : StrictMono (l6closed_4_sortedTuple a) := by
  intro k l hkl
  have hk := k.isLt
  have hl := l.isLt
  rw [l6closed_4_sortedTuple,l6closed_4_block_less]
  by_cases h : k.val/2=l.val/2
  · right
    have hp : k.val%2=0 ∧ l.val%2=1 := by omega
    have he : (⟨l.val/2, by omega⟩ : Fin 4)=⟨k.val/2, by omega⟩ := Fin.ext h.symm
    refine ⟨h,?_⟩
    have ke : (⟨k.val%2, by omega⟩ : Fin 2)=0 := Fin.ext hp.1
    have le : (⟨l.val%2, by omega⟩ : Fin 2)=1 := Fin.ext hp.2
    rw [he,ke,le]
    exact l6closed_4_sb_increasing a _
  · left
    omega
private theorem l6closed_4_sorted_image (a : Fin 4 → Fin 6) :
    Finset.univ.image (l6closed_4_sortedTuple a) = l6closed_4_face a := by
  ext w
  by_cases h0 : a 0=5 <;> by_cases h1 : a 1=5 <;>
    by_cases h2 : a 2=5 <;> by_cases h3 : a 3=5
  all_goals simp [Finset.mem_image,l6closed_4_face,Fin.exists_fin_succ,l6closed_4_sortedTuple,l6closed_4_bt,l6closed_4_sb,l6closed_4_hb,
    HexTuple,l6closed_4_step,h0,h1,h2,h3]
  all_goals tauto
private theorem l6closed_4_sorted_emb (a : Fin 4 → Fin 6) :
    l6closed_4_sortedTuple a = (l6closed_4_face a).orderEmbOfFin (l6closed_4_face_card a) := by
  apply Finset.orderEmbOfFin_unique (l6closed_4_face_card a)
  · intro k
    rw [← l6closed_4_sorted_image a]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  · exact l6closed_4_sorted_strict a
private def l6closed_4_relabelHom (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun c := relabel f c
  map_zero' := by simp [relabel]
  map_add' c d := Finsupp.sum_add_index'
    (fun s => zero_smul ℤ (listedFace (fun i : Fin s.card => f (s.orderEmbOfFin rfl i))))
    (fun s a b => add_smul a b _)
private theorem l6closed_4_relabel_single (f : ℕ → ℕ) (s : Finset ℕ) (n : ℕ)
    (h : s.card=n) (c : ℤ) :
    relabel f (Finsupp.single s c) =
      c • listedFace (fun i : Fin n => f (s.orderEmbOfFin h i)) := by
  subst n
  rw [relabel,Finsupp.sum_single_index (by simp)]
private def l6closed_4_two (v : Fin 6) : Fin 6 := ⟨(v.val+2)%6,Nat.mod_lt _ (by omega)⟩
private def l6closed_4_twoE : Fin 6 ≃ Fin 6 where
  toFun := l6closed_4_two
  invFun v := ⟨(v.val+4)%6,Nat.mod_lt _ (by omega)⟩
  left_inv v := by apply Fin.ext; have h := v.isLt; dsimp [l6closed_4_two]; omega
  right_inv v := by apply Fin.ext; have h := v.isLt; dsimp [l6closed_4_two]; omega
private def l6closed_4_shiftAll : (Fin 4 → Fin 6) ≃ (Fin 4 → Fin 6) :=
  Equiv.piCongrRight (fun _ => l6closed_4_twoE)
private theorem l6closed_4_shiftAll_apply (a : Fin 4 → Fin 6) (i : Fin 4) : l6closed_4_shiftAll a i = l6closed_4_two (a i) := rfl
private def l6closed_4_shiftedB (a : Fin 4 → Fin 6) (i : Fin 4) (j : Fin 2) : Fin 6 := l6closed_4_two (l6closed_4_sb a i j)
private theorem l6closed_4_shift_block (b : Fin 4 → Fin 2 → Fin 6) :
    (fun k : Fin 8 => ShiftVertex (l6closed_4_bt b k)) = l6closed_4_bt (fun i j => l6closed_4_two (b i j)) := by
  funext k
  have hk := k.isLt
  have hv := (b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).isLt
  have hx : l6closed_4_bt b k < 24 := by dsimp [l6closed_4_bt]; omega
  dsimp [l6closed_4_bt,l6closed_4_two]
  unfold ShiftVertex
  split_ifs <;> omega
private theorem l6closed_4_shift_hex (a : Fin 4 → Fin 6) :
    (fun k : Fin 8 => ShiftVertex (HexTuple a k)) = HexTuple (l6closed_4_shiftAll a) := by
  rw [l6closed_4_hex_bt,l6closed_4_shift_block,l6closed_4_hex_bt]
  congr 1
  funext i j
  fin_cases j
  · simp [l6closed_4_hb,l6closed_4_shiftAll_apply]
  · simp only [l6closed_4_hb,Fin.reduceEq,ite_false,l6closed_4_shiftAll_apply]
    apply Fin.ext
    have h := (a i).isLt
    dsimp [l6closed_4_step,l6closed_4_two]
    omega
private theorem l6closed_4_shifted_image (a : Fin 4 → Fin 6) :
    Finset.univ.image (fun k => ShiftVertex (l6closed_4_sortedTuple a k)) = l6closed_4_face (l6closed_4_shiftAll a) := by
  calc
    _ = (Finset.univ.image (l6closed_4_sortedTuple a)).image ShiftVertex :=
      (Finset.image_image (f := l6closed_4_sortedTuple a) (g := ShiftVertex)
        (s := (Finset.univ : Finset (Fin 8)))).symm
    _ = _ := by
      rw [l6closed_4_sorted_image,l6closed_4_face,Finset.image_image]
      exact congrArg (fun f : Fin 8 → ℕ => Finset.univ.image f) (l6closed_4_shift_hex a)
private theorem l6closed_4_shift_sign_local : ∀ v : Fin 6,
    l6closed_4_eps v * (if l6closed_4_two (if v=5 then (5:Fin 6) else l6closed_4_step v) <
      l6closed_4_two (if v=5 then (0:Fin 6) else v) then (-1:ℤ) else 1) = l6closed_4_eps (l6closed_4_two v) := by
  decide +kernel
private theorem l6closed_4_shifted_sign (a : Fin 4 → Fin 6) :
    l6closed_4_signC (HexTuple a) * l6closed_4_signC (fun k => ShiftVertex (l6closed_4_sortedTuple a k)) =
      l6closed_4_signC (HexTuple (l6closed_4_shiftAll a)) := by
  rw [l6closed_4_sign_hex]
  change (∏ i : Fin 4, l6closed_4_eps (a i)) * l6closed_4_signC (fun k => ShiftVertex (l6closed_4_bt (l6closed_4_sb a) k)) = _
  rw [l6closed_4_shift_block,l6closed_4_sign_block,l6closed_4_sign_hex]
  change (∏ i : Fin 4, l6closed_4_eps (a i)) *
      (∏ i : Fin 4, if l6closed_4_two (l6closed_4_sb a i 1) < l6closed_4_two (l6closed_4_sb a i 0) then (-1:ℤ) else 1) =
      ∏ i : Fin 4, l6closed_4_eps (l6closed_4_shiftAll a i)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [l6closed_4_sb,l6closed_4_hb,Fin.reduceEq,ite_false,ite_true,l6closed_4_shiftAll_apply]
  exact l6closed_4_shift_sign_local (a i)
private theorem l6closed_4_relabel_facet (a : Fin 4 → Fin 6) :
    relabel ShiftVertex (listedFace (HexTuple a)) = listedFace (HexTuple (l6closed_4_shiftAll a)) := by
  rw [l6closed_4_listed_eq]
  change relabel ShiftVertex (Finsupp.single (l6closed_4_face a) (l6closed_4_signC (HexTuple a))) = _
  rw [l6closed_4_relabel_single ShiftVertex (l6closed_4_face a) 8 (l6closed_4_face_card a)]
  rw [← l6closed_4_sorted_emb a]
  rw [l6closed_4_listed_eq,l6closed_4_listed_eq,Finsupp.smul_single]
  rw [l6closed_4_shifted_image]
  congr 1
  exact l6closed_4_shifted_sign a
private theorem l6closed_4_invariant : relabel ShiftVertex HexCycle=HexCycle := by
  change l6closed_4_relabelHom ShiftVertex HexCycle=HexCycle
  rw [HexCycle,map_sum]
  change (∑ a : Fin 4 → Fin 6, relabel ShiftVertex (listedFace (HexTuple a))) =
    ∑ a : Fin 4 → Fin 6, listedFace (HexTuple a)
  exact Fintype.sum_equiv l6closed_4_shiftAll _ _ l6closed_4_relabel_facet

private theorem Sierksma.hexagon_join_cycle :
    Homogeneous 8 HexCycle ∧ IsCycle HexCycle ∧
    relabel ShiftVertex HexCycle=HexCycle ∧
    (∀ s ∈ HexCycle.support, ∀ v ∈ s, v<24 ∧ ShiftVertex v ∉ s ∧
      ShiftVertex (ShiftVertex v) ∉ s) := by
  exact ⟨l6closed_4_homogeneous,l6closed_4_cycle,l6closed_4_invariant,l6closed_4_orbit_support⟩
end
end

section
open PLDegree
open scoped BigOperators
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

private theorem PLDegree.signed_count_relabel {V : Type*} [LinearOrder V] {n : ℕ}
    (f : V → V) (hf : Function.Injective f) (H : V → Fin n → ℝ) (c : Chain V) :
    signedCount H (relabel f c) = signedCount (H ∘ f) c := by
  classical
  have hsign : ∀ {k : ℕ} (p : Equiv.Perm (Fin k)) (t : Fin k → V),
      StrictMono t → listSign (t ∘ p) = (p.sign : ℤ) := by
    intro k p t ht
    unfold listSign
    simp only [Function.comp_apply, ht.lt_iff_lt]
    rw [p.sign_eq_prod_prod_Ioi]
    simp only [Units.coe_prod]
    rw [← Finset.prod_const, Finset.prod_filter]
    rw [← Finset.univ_product_univ, Finset.prod_product]
    apply Finset.prod_congr rfl
    intro i hi
    rw [show Finset.Ioi i = Finset.univ.filter (fun j => i < j) by ext; simp,
      Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hij : i < j
    · have hne : p i ≠ p j := p.injective.ne hij.ne
      rcases lt_or_gt_of_ne hne with hp | hp <;> simp [hij, hp, hp.not_gt]
    · simp [hij]
  have hface : ∀ s : Finset V,
      listSign (fun i : Fin s.card => f (s.orderEmbOfFin rfl i)) *
        simplexDegree H (s.image f) = simplexDegree (H ∘ f) s := by
    intro s
    have hcard : (s.image f).card = s.card := Finset.card_image_of_injective s hf
    by_cases hs : s.card = n + 1
    · let T := s.image f
      have hT : T.card = n + 1 := hcard.trans hs
      let e : Fin (n+1) → Fin (n+1) := fun i =>
        (T.orderIsoOfFin hT).symm ⟨f (s.orderEmbOfFin hs i),
          Finset.mem_image_of_mem f (s.orderEmbOfFin_mem hs i)⟩
      have he : Function.Injective e := by
        intro i j hij
        have hv := congrArg (fun x => ((T.orderIsoOfFin hT x : T) : V)) hij
        have hfv : f (s.orderEmbOfFin hs i) = f (s.orderEmbOfFin hs j) := by
          simpa [e] using hv
        exact (s.orderEmbOfFin hs).injective (hf hfv)
      let p : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective e
        ⟨he, Finite.injective_iff_surjective.mp he⟩
      have hp : ∀ i, T.orderEmbOfFin hT (p i) = f (s.orderEmbOfFin hs i) := by
        intro i
        change (((T.orderIsoOfFin hT) (e i) : T) : V) = _
        simp [e]
      have hls : listSign (fun i : Fin s.card => f (s.orderEmbOfFin rfl i)) =
          (p.sign : ℤ) := by
        have heq : (fun i : Fin (n+1) => f (s.orderEmbOfFin hs i)) =
            T.orderEmbOfFin hT ∘ p := by funext i; exact (hp i).symm
        have hh := hsign p (T.orderEmbOfFin hT) (T.orderEmbOfFin hT).strictMono
        rw [← heq] at hh
        have hcast : ∀ {k l : ℕ} (h : k = l) (t : Fin l → V),
            listSign (t ∘ Fin.cast h) = listSign t := by
          intro k l h t
          subst l
          rfl
        have heq' : (fun i : Fin s.card => f (s.orderEmbOfFin rfl i)) =
            (fun i : Fin (n+1) => f (s.orderEmbOfFin hs i)) ∘ Fin.cast hs := by
          funext i
          apply congrArg f
          exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
        rw [heq', hcast]
        exact hh
      let M := augmentedMatrix H T hT
      let N := augmentedMatrix (H ∘ f) s hs
      have hMN : N = M.submatrix p (Equiv.refl _) := by
        ext i j
        simp only [N, M, augmentedMatrix, Matrix.submatrix_apply, Equiv.refl_apply,
          Function.comp_apply, hp]
      have hd : N.det = (p.sign : ℝ) * M.det := by
        rw [hMN]
        exact Matrix.det_permute p M
      have hb : ∀ i, barycentric (H ∘ f) s hs i = barycentric H T hT (p i) := by
        intro i
        unfold barycentric
        change Matrix.vecMul (originRow n) N⁻¹ i = Matrix.vecMul (originRow n) M⁻¹ (p i)
        rw [hMN, Matrix.inv_submatrix_equiv]
        rfl
      have hpos : (∀ i, 0 < barycentric (H ∘ f) s hs i) ↔
          (∀ i, 0 < barycentric H T hT i) := by
        simp only [hb]
        constructor
        · intro hh i
          simpa using hh (p.symm i)
        · intro hh i
          exact hh (p i)
      have hdn : N.det ≠ 0 ↔ M.det ≠ 0 := by
        rw [hd]
        simp
      have hsgn : (SignType.sign N.det : ℤ) =
          (p.sign : ℤ) * (SignType.sign M.det : ℤ) := by
        rw [hd]
        rcases Int.units_eq_one_or p.sign with hp1 | hpm
        · simp [hp1]
        · simp [hpm, Left.sign_neg, SignType.coe_neg]
      unfold simplexDegree
      rw [dif_pos hs, dif_pos hT]
      change (listSign (fun i : Fin s.card => f (s.orderEmbOfFin rfl i))) *
          (if M.det ≠ 0 ∧ ∀ i, 0 < barycentric H T hT i then
            (SignType.sign M.det : ℤ) else 0) =
          if N.det ≠ 0 ∧ ∀ i, 0 < barycentric (H ∘ f) s hs i then
            (SignType.sign N.det : ℤ) else 0
      simp only [hls, hdn, hpos]
      split_ifs <;> simp [hsgn]
    · simp [simplexDegree, hs, hcard]
  unfold signedCount evaluate relabel
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by ring)]
  apply Finsupp.sum_congr
  intro s a
  rw [Finsupp.sum_smul_index (fun _ => by simp)]
  unfold listedFace
  rw [Finsupp.sum_single_index (by simp)]
  have himage : Finset.univ.image (fun i : Fin s.card => f (s.orderEmbOfFin rfl i)) =
      s.image f := by
    change Finset.image (f ∘ s.orderEmbOfFin rfl) Finset.univ = _
    rw [← Finset.image_image, Finset.image_orderEmbOfFin_univ]
  convert congrArg (fun b : ℤ => c s * b) (hface s) using 1
  simp only [mul_assoc]
  congr 2
  apply congrArg (simplexDegree H)
  apply Finset.ext
  intro v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨s.orderEmbOfFin rfl i, s.orderEmbOfFin_mem rfl i, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(s.orderIsoOfFin rfl).symm ⟨w,hw⟩, Finset.mem_univ _, by simp [Finset.orderEmbOfFin]⟩
end

section
open PLDegree
open scoped BigOperators

private theorem PLDegree.augmented_linear_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
  ∃ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, B.det = A.det ∧
    Matrix.vecMul (originRow n) B = originRow n ∧
    ∀ w : Fin n → ℝ, ∀ a : ℝ,
      Matrix.vecMul (augment w a) B = augment (A.mulVec w) a := by
  classical
  let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
  let C : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    Matrix.fromBlocks A.transpose 0 0 1
  let B := C.submatrix e.symm e.symm
  have hdet : B.det = A.det := by
    dsimp [B, C]
    rw [Matrix.det_submatrix_equiv_self]
    simp [Matrix.det_fromBlocks_zero₂₁]
  have ha : ∀ (w : Fin n → ℝ) (a : ℝ),
      Matrix.vecMul (augment w a) B = augment (A.mulVec w) a := by
    intro w a
    have hh : augment w a ∘ e = Sum.elim w (fun _ => a) := by
      funext i
      cases i with
      | inl i => simp [e, augment, i.isLt]
      | inr i => fin_cases i; simp [e, augment]
    dsimp [B]
    rw [Matrix.submatrix_vecMul_equiv]
    change (Matrix.vecMul (augment w a ∘ e) C) ∘ e.symm = _
    rw [hh]
    dsimp [C]
    rw [Matrix.vecMul_fromBlocks]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.vecMul_zero, Matrix.vecMul_one, add_zero, zero_add,
      Matrix.vecMul_transpose]
    apply funext
    intro i
    induction i using Fin.lastCases with
    | last => simp [e, augment]
    | cast i => simp [e, augment, i.isLt]
  refine ⟨B, hdet, ?_, ha⟩
  have hh : originRow n = augment (0 : Fin n → ℝ) 1 := by
    funext i
    induction i using Fin.lastCases with
    | last => simp [originRow, augment]
    | cast i => simp [originRow, augment, i.isLt, Fin.castSucc_ne_last]
  rw [hh, ha]
  simp
end

section
open PLDegree
open scoped BigOperators

theorem PLDegree.positive_linear_degree_invariant {V : Type*} [LinearOrder V] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : 0<A.det) (F : V → Fin n → ℝ) :
    (∀ s : Finset V, simplexDegree (fun v => A.mulVec (F v)) s=simplexDegree F s) ∧
    (∀ c : Chain V, signedCount (fun v => A.mulVec (F v)) c=signedCount F c) := by
  classical
  obtain ⟨B, hB, ho, hr⟩ := PLDegree.augmented_linear_matrix A
  have hsimplex : ∀ s : Finset V,
      simplexDegree (fun v => A.mulVec (F v)) s = simplexDegree F s := by
    intro s
    by_cases hs : s.card = n+1
    · let M := augmentedMatrix F s hs
      let N := augmentedMatrix (fun v => A.mulVec (F v)) s hs
      have hN : N = M*B := by
        ext i j
        exact (congrFun (hr (F (s.orderEmbOfFin hs i)) 1) j).symm
      have hd : N.det = M.det*A.det := by rw [hN, Matrix.det_mul, hB]
      have hnonzero : N.det ≠ 0 ↔ M.det ≠ 0 := by
        rw [hd, mul_ne_zero_iff]
        exact and_iff_left (ne_of_gt hA)
      by_cases hm : M.det ≠ 0
      · have huM : IsUnit M.det := isUnit_iff_ne_zero.mpr hm
        have huN : IsUnit N.det := isUnit_iff_ne_zero.mpr (hnonzero.mpr hm)
        have hc : barycentric (fun v => A.mulVec (F v)) s hs = barycentric F s hs := by
          apply Matrix.vecMul_injective_of_isUnit ((N.isUnit_iff_isUnit_det).mpr huN)
          change Matrix.vecMul (Matrix.vecMul (originRow n) N⁻¹) N =
            Matrix.vecMul (Matrix.vecMul (originRow n) M⁻¹) N
          rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul N huN, Matrix.vecMul_one]
          rw [hN, ← Matrix.vecMul_vecMul (Matrix.vecMul (originRow n) M⁻¹) M B,
            Matrix.vecMul_vecMul (originRow n) M⁻¹ M,
            Matrix.nonsing_inv_mul M huM, Matrix.vecMul_one, ho]
        have hsign : SignType.sign N.det = SignType.sign M.det := by
          rw [hd, sign_mul, sign_pos hA, mul_one]
        simp only [simplexDegree, dif_pos hs]
        change (if N.det ≠ 0 ∧ ∀ i, 0 < barycentric (fun v => A.mulVec (F v)) s hs i
            then (SignType.sign N.det : ℤ) else 0) =
          (if M.det ≠ 0 ∧ ∀ i, 0 < barycentric F s hs i
            then (SignType.sign M.det : ℤ) else 0)
        simp only [hnonzero, hc, hsign]
      · have hn : N.det = 0 := not_ne_iff.mp (mt hnonzero.mp hm)
        have hm0 : M.det = 0 := not_ne_iff.mp hm
        simp only [simplexDegree, dif_pos hs]
        change (if N.det ≠ 0 ∧ _ then _ else _) = (if M.det ≠ 0 ∧ _ then _ else _)
        simp [hn, hm0]
    · simp [simplexDegree, hs]
  refine ⟨hsimplex, ?_⟩
  intro c
  unfold signedCount evaluate
  congr 1
  funext s a
  rw [hsimplex]
end

section
open Sierksma
open scoped BigOperators
set_option maxHeartbeats 800000

private theorem Sierksma.R8_orientation_preserving :
    (∀ w : W8, R8 (R8 (R8 w))=w) ∧
    ∃ A : Matrix (Fin 8) (Fin 8) ℝ, A.det=1 ∧ ∀ w : W8, A.mulVec w=R8 w := by
  have hc : ∀ w : W8, R8 (R8 (R8 w))=w := by
    intro w
    funext j
    fin_cases j <;> simp [R8] <;> ring
  let A : Matrix (Fin 8) (Fin 8) ℝ := fun i j =>
    if i.val<4 then (if j.val=i.val+4 then -1 else 0)
    else (if j.val=i.val-4 then 1 else if j=i then -1 else 0)
  have hm : ∀ w : W8, A.mulVec w=R8 w := by
    intro w
    funext j
    fin_cases j <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,A,R8,sub_eq_add_neg]
  have hcube : A*A*A=1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hm,hm,hm,hc,Matrix.one_mulVec]
  have hdet : A.det=1 := by
    have hh := congrArg Matrix.det hcube
    rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_one] at hh
    have hp : 0 < A.det^2+A.det+1 := by nlinarith [sq_nonneg (A.det+1/2)]
    have he : (A.det-1)*(A.det^2+A.det+1)=0 := by nlinarith [hh]
    rcases mul_eq_zero.mp he with he | he
    · linarith
    · exact (ne_of_gt hp he).elim
  exact ⟨hc,A,hdet,hm⟩
end

section
open Sierksma
set_option maxHeartbeats 1000000

private theorem Sierksma.engine_shift_equivariance :
    (∀ v : ℕ, ShiftVertex (ShiftVertex (ShiftVertex v))=v) ∧
    Function.Injective ShiftVertex ∧
    ∀ x : EngineParams, ∀ v : ℕ, EngineMap x (ShiftVertex v)=R8 (EngineMap x v) := by
  have hc : ∀ v : ℕ, ShiftVertex (ShiftVertex (ShiftVertex v))=v := by
    intro v
    by_cases hv : v<27
    · interval_cases v <;> norm_num [ShiftVertex]
    · have hv24 : ¬v<24 := by omega
      simp [ShiftVertex,hv,hv24]
  have hR0 : R8 (0 : W8)=0 := by
    funext j
    unfold R8
    split_ifs <;> simp
  refine ⟨hc,?_,?_⟩
  · intro a b hab
    have hh := congrArg (fun v => ShiftVertex (ShiftVertex v)) hab
    simpa only [hc] using hh
  · intro x v
    by_cases hv : v<27
    · interval_cases v <;>
        simp [ShiftVertex,EngineMap,RPower,Function.iterate_succ_apply',
          Sierksma.R8_orientation_preserving.1]
    · have hv24 : ¬v<24 := by omega
      simp [ShiftVertex,EngineMap,hv,hv24,hR0]
end

section
set_option autoImplicit false

open Set Filter Topology

private theorem PLDegree.polynomial_nonzero_open_dense {k : ℕ}
    (p : MvPolynomial (Fin k) ℝ) (hp : p ≠ 0) :
    IsOpen {x : Fin k → ℝ | MvPolynomial.eval x p ≠ 0} ∧
    Dense {x : Fin k → ℝ | MvPolynomial.eval x p ≠ 0} := by
  have ha : AnalyticOnNhd ℝ (fun x : Fin k → ℝ => MvPolynomial.eval x p) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial p
  have hc : Continuous (fun x : Fin k → ℝ => MvPolynomial.eval x p) :=
    continuousOn_univ.mp ha.continuousOn
  refine ⟨isOpen_ne.preimage hc, dense_iff_inter_open.mpr ?_⟩
  intro U hU hUne
  obtain ⟨z, hz⟩ := hUne
  by_contra hnone
  have hzero : ∀ x ∈ U, MvPolynomial.eval x p = 0 := by
    intro x hx
    by_contra hne
    exact hnone ⟨x, hx, hne⟩
  have hevent : (fun x : Fin k → ℝ => MvPolynomial.eval x p) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hU.mem_nhds hz] with x hx
    exact hzero x hx
  have heq : (fun x : Fin k → ℝ => MvPolynomial.eval x p) = 0 :=
    ha.eq_of_eventuallyEq analyticOnNhd_const hevent
  apply hp
  apply MvPolynomial.funext
  intro x
  have hh := congrFun heq x
  simpa using hh
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
set_option maxHeartbeats 800000
private theorem l6closed_11_matrix_agree (s : Finset ℕ) (F G : ℕ → W8)
    (h : ∀ v ∈ s, F v=G v) (hs : s.card=9) :
    augmentedMatrix F s hs=augmentedMatrix G s hs := by
  ext i j
  simp only [augmentedMatrix]
  rw [h _ (s.orderEmbOfFin_mem hs i)]
private theorem l6closed_11_linear_agree (s : Finset ℕ) (F G : ℕ → W8)
    (h : ∀ v ∈ s, F v=G v) : linearDet F s=linearDet G s := by
  unfold linearDet
  split_ifs with hs
  · congr 1
    ext i j
    rw [h _ (s.orderEmbOfFin_mem hs i)]
  · rfl
private theorem l6closed_11_simplex_agree (s : Finset ℕ) (F G : ℕ → W8)
    (h : ∀ v ∈ s, F v=G v) :
    simplexDegree F s=simplexDegree G s ∧ (SimplexGP F s ↔ SimplexGP G s) := by
  classical
  have haug : augmentedDet F s=augmentedDet G s := by
    unfold augmentedDet
    split_ifs with hs
    · rw [l6closed_11_matrix_agree s F G h hs]
    · rfl
  have hlin : ∀ v ∈ s, linearDet F (s.erase v)=linearDet G (s.erase v) := by
    intro v _
    apply l6closed_11_linear_agree
    intro u hu
    exact h u (Finset.mem_of_mem_erase hu)
  constructor
  · by_cases hs : s.card=9
    · simp only [simplexDegree,dif_pos hs,barycentric,l6closed_11_matrix_agree s F G h hs]
      congr 1
    · simp only [simplexDegree,dif_neg hs]
  · unfold SimplexGP
    have dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq ℕ) =
        instDecidableEqNat := Subsingleton.elim _ _
    rw [dEq]
    simp only [haug]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply forall_congr'
    intro v
    apply forall_congr'
    intro hv
    have hh : linearDet F (s.erase v)=linearDet G (s.erase v) :=
      l6closed_11_linear_agree _ F G (fun u hu => h u (Finset.mem_of_mem_erase hu))
    rw [hh]
private theorem l6closed_11_chain_agree (c : Chain ℕ) (F G : ℕ → W8)
    (h : ∀ s ∈ c.support, ∀ v ∈ s, F v=G v) :
    signedCount F c=signedCount G c ∧ (ChainGP F c ↔ ChainGP G c) := by
  constructor
  · unfold signedCount evaluate
    apply Finsupp.sum_congr
    intro s hs
    rw [(l6closed_11_simplex_agree s F G (h s hs)).1]
  · unfold ChainGP
    apply forall_congr'
    intro s
    apply forall_congr'
    intro hs
    exact (l6closed_11_simplex_agree s F G (h s hs)).2
private theorem l6closed_11_cone_supported (c : Chain ℕ) (y : ℕ) (t : Finset ℕ)
    (ht : t ∈ (cone y c).support) : ∃ s ∈ c.support, y ∉ s ∧ t=insert y s := by
  by_contra hn
  have hh : (cone y c) t=0 := by
    unfold cone
    rw [Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [Finsupp.smul_apply,smul_eq_mul,faceCone]
    split_ifs with hy
    · simp
    · have hne : insert y s≠t := by
        intro he
        exact hn ⟨s,hs,hy,he.symm⟩
      rw [Finsupp.single_apply]
      split_ifs with he
      · apply False.elim
        apply hne
        ext v
        rw [← he]
        simp only [Finset.mem_insert]
      · simp
  exact (Finsupp.mem_support_iff.mp ht) hh
theorem Sierksma.l6_chain_support_tools :
    (∀ (s : Finset ℕ) (F G : ℕ → W8), (∀ v ∈ s, F v=G v) →
      simplexDegree F s=simplexDegree G s ∧ (SimplexGP F s ↔ SimplexGP G s)) ∧
    (∀ (c : Chain ℕ) (F G : ℕ → W8),
      (∀ s ∈ c.support, ∀ v ∈ s, F v=G v) →
      signedCount F c=signedCount G c ∧ (ChainGP F c ↔ ChainGP G c)) ∧
    (∀ (c : Chain ℕ) (y : ℕ) (t : Finset ℕ), t ∈ (cone y c).support →
      ∃ s ∈ c.support, y ∉ s ∧ t=insert y s) := by
  exact ⟨l6closed_11_simplex_agree,l6closed_11_chain_agree,l6closed_11_cone_supported⟩
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private theorem l6closed_12_row_det_image {m : ℕ} (f : ℕ → ℕ) (hf : Function.Injective f)
    (F : ℕ → Fin m → ℝ) (s : Finset ℕ) (hs : s.card=m)
    (ht : (s.image f).card=m) :
    (Matrix.det (fun i j : Fin m => F ((s.image f).orderEmbOfFin ht i) j) ≠ 0) ↔
      (Matrix.det (fun i j : Fin m => F (f (s.orderEmbOfFin hs i)) j) ≠ 0) := by
  let T := s.image f
  let e : Fin m → Fin m := fun i =>
    (T.orderIsoOfFin ht).symm ⟨f (s.orderEmbOfFin hs i),
      Finset.mem_image_of_mem f (s.orderEmbOfFin_mem hs i)⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg (fun x => ((T.orderIsoOfFin ht x : T) : ℕ)) hij
    have hfv : f (s.orderEmbOfFin hs i)=f (s.orderEmbOfFin hs j) := by simpa [e] using hv
    exact (s.orderEmbOfFin hs).injective (hf hfv)
  let p : Equiv.Perm (Fin m) := Equiv.ofBijective e ⟨he,Finite.surjective_of_injective he⟩
  have hp : ∀ i, T.orderEmbOfFin ht (p i)=f (s.orderEmbOfFin hs i) := by
    intro i
    change (((T.orderIsoOfFin ht) (e i) : T) : ℕ)=_
    simp [e]
  let M : Matrix (Fin m) (Fin m) ℝ := fun i j => F (T.orderEmbOfFin ht i) j
  have hn : (fun i j : Fin m => F (f (s.orderEmbOfFin hs i)) j)=M.submatrix p id := by
    ext i j
    change F (f (s.orderEmbOfFin hs i)) j=F (T.orderEmbOfFin ht (p i)) j
    rw [hp]
  rw [hn,Matrix.det_permute]
  change M.det≠0 ↔ _
  simp
private theorem l6closed_12_aug_image (f : ℕ → ℕ) (hf : Function.Injective f) (F : ℕ → W8)
    (s : Finset ℕ) : augmentedDet F (s.image f)≠0 ↔ augmentedDet (F ∘ f) s≠0 := by
  have hc : (s.image f).card=s.card := Finset.card_image_of_injective s hf
  by_cases hs : s.card=9
  · have ht : (s.image f).card=9 := hc.trans hs
    simp only [augmentedDet,dif_pos hs,dif_pos ht,augmentedMatrix]
    exact l6closed_12_row_det_image f hf (fun v => augment (F v) 1) s hs ht
  · simp [augmentedDet,hs,hc]
private theorem l6closed_12_lin_image (f : ℕ → ℕ) (hf : Function.Injective f) (F : ℕ → W8)
    (s : Finset ℕ) : linearDet F (s.image f)≠0 ↔ linearDet (F ∘ f) s≠0 := by
  have hc : (s.image f).card=s.card := Finset.card_image_of_injective s hf
  by_cases hs : s.card=8
  · have ht : (s.image f).card=8 := hc.trans hs
    simp only [linearDet,dif_pos hs,dif_pos ht]
    exact l6closed_12_row_det_image f hf F s hs ht
  · simp [linearDet,hs,hc]
theorem Sierksma.l6_gp_image (f : ℕ → ℕ) (hf : Function.Injective f)
    (F : ℕ → W8) (s : Finset ℕ) :
    SimplexGP F (s.image f) ↔ SimplexGP (F ∘ f) s  := by
  unfold SimplexGP
  have dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq ℕ)=instDecidableEqNat :=
    Subsingleton.elim _ _
  rw [dEq]
  rw [Finset.card_image_of_injective s hf,l6closed_12_aug_image f hf F s]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h v hv
    have H := h (f v) (Finset.mem_image_of_mem f hv)
    rw [← Finset.image_erase hf s v] at H
    exact (l6closed_12_lin_image f hf F (s.erase v)).mp H
  · intro h v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    rw [← Finset.image_erase hf s u]
    exact (l6closed_12_lin_image f hf F (s.erase u)).mpr (h u hu)
end
end

section
open PLDegree Sierksma
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private def l6closed_13_C (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private def l6closed_13_L (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := relabel f
  map_zero' := by simp [relabel]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private theorem l6closed_13_inc_list (s : Finset ℕ) :
    listedFace (s.orderEmbOfFin rfl) = Finsupp.single s 1 := by
  unfold listedFace
  have him : Finset.univ.image (s.orderEmbOfFin rfl) = s := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact s.orderEmbOfFin_mem rfl i
    · intro hv
      exact ⟨(s.orderIsoOfFin rfl).symm ⟨v,hv⟩, by simp [Finset.orderEmbOfFin]⟩
  congr 1
  · convert him using 1 <;> ext v <;> simp only [Finset.mem_image]
  · unfold listSign
    have hf : (Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij h
      exact (not_lt_of_ge ((s.orderEmbOfFin rfl).strictMono (Finset.mem_filter.mp h).2.1).le)
        (Finset.mem_filter.mp h).2.2
    calc
      _ = (-1 : ℤ)^((Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1)).card) := by
        congr 2
        ext ij
        simp only [Finset.mem_filter]
      _ = 1 := by rw [hf]; simp
private theorem l6closed_13_face_nat (f : ℕ → ℕ) (hf : Function.Injective f) (y : ℕ) (s : Finset ℕ) :
    l6closed_13_L f (l6closed_13_C y (Finsupp.single s 1)) = l6closed_13_C (f y) (l6closed_13_L f (Finsupp.single s 1)) := by
  rw [← l6closed_13_inc_list s]
  by_cases hy : y ∈ s
  · have hn : f y ∈ s.image f := Finset.mem_image_of_mem f hy
    have hleft : cone y (listedFace (s.orderEmbOfFin rfl))=0 := by
      rw [l6closed_13_inc_list,cone,Finsupp.sum_single_index (by simp)]
      simp [faceCone,hy]
    change relabel f (cone y (listedFace _)) = cone (f y) (relabel f (listedFace _))
    rw [hleft,PLDegree.relabel_listed_face _ (s.orderEmbOfFin rfl).injective f hf]
    rw [relabel,Finsupp.sum_zero_index]
    unfold listedFace cone
    rw [Finsupp.sum_single_index (by simp)]
    have hzero : faceCone (f y) (Finset.univ.image (f ∘ s.orderEmbOfFin rfl))=0 := by
      unfold faceCone
      split_ifs with hp
      · rfl
      · exfalso
        apply hp
        refine Finset.mem_image.mpr ⟨(s.orderIsoOfFin rfl).symm ⟨y,hy⟩,Finset.mem_univ _,?_⟩
        simp [Function.comp_apply,Finset.orderEmbOfFin]
    convert (show 0 = (listSign (f ∘ s.orderEmbOfFin rfl)) •
      faceCone (f y) (Finset.univ.image (f ∘ s.orderEmbOfFin rfl)) by rw [hzero]; simp) using 1
    congr 2
    ext v
    simp only [Finset.mem_image]
  · have hy' : ∀ i : Fin s.card, s.orderEmbOfFin rfl i≠y := by
      intro i he
      exact hy (he ▸ s.orderEmbOfFin_mem rfl i)
    change relabel f (cone y (listedFace _)) = cone (f y) (relabel f (listedFace _))
    rw [PLDegree.cone_listed_face y _ (s.orderEmbOfFin rfl).injective hy',
      PLDegree.relabel_listed_face _ (Fin.cons_injective_of_injective
        (by rintro ⟨i,hi⟩; exact hy' i hi) (s.orderEmbOfFin rfl).injective) f hf,
      PLDegree.relabel_listed_face _ (s.orderEmbOfFin rfl).injective f hf,
      PLDegree.cone_listed_face (f y) _ (hf.comp (s.orderEmbOfFin rfl).injective)
        (fun i hi => hy' i (hf hi))]
    congr 1
    funext i
    cases i using Fin.cases <;> rfl
theorem Sierksma.l6_relabel_cone (f : ℕ → ℕ) (hf : Function.Injective f)
    (y : ℕ) (c : Chain ℕ) :
    relabel f (cone y c)=cone (f y) (relabel f c)  := by
  change l6closed_13_L f (l6closed_13_C y c)=l6closed_13_C (f y) (l6closed_13_L f c)
  have hc := Finsupp.sum_single c
  rw [← hc]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hs : Finsupp.single s (c s)=c s • Finsupp.single s 1 := by simp
  rw [hs,map_zsmul,map_zsmul,map_zsmul,map_zsmul,l6closed_13_face_nat f hf y s]
end
end

section
open PLDegree Sierksma
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private def l6closed_14_C (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private def l6closed_14_L (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := relabel f
  map_zero' := by simp [relabel]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private theorem l6closed_14_inc_list (s : Finset ℕ) :
    listedFace (s.orderEmbOfFin rfl) = Finsupp.single s 1 := by
  unfold listedFace
  have him : Finset.univ.image (s.orderEmbOfFin rfl) = s := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact s.orderEmbOfFin_mem rfl i
    · intro hv
      exact ⟨(s.orderIsoOfFin rfl).symm ⟨v,hv⟩, by simp [Finset.orderEmbOfFin]⟩
  congr 1
  · convert him using 1 <;> ext v <;> simp only [Finset.mem_image]
  · unfold listSign
    have hf : (Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij h
      exact (not_lt_of_ge ((s.orderEmbOfFin rfl).strictMono (Finset.mem_filter.mp h).2.1).le)
        (Finset.mem_filter.mp h).2.2
    calc
      _ = (-1 : ℤ)^((Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1)).card) := by
        congr 2
        ext ij
        simp only [Finset.mem_filter]
      _ = 1 := by rw [hf]; simp

private theorem l6closed_14_nat_dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq ℕ)=instDecidableEqNat :=
  Subsingleton.elim _ _
private def l6closed_14_K (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := link y
  map_zero' := by simp [link]
  map_add' a b := Finsupp.sum_add_index'
    (fun _ => by split_ifs <;> simp) (fun _ _ _ => by split_ifs <;> simp [add_smul])
private theorem l6closed_14_incidence_sq (s : Finset ℕ) (y : ℕ) : incidence s y * incidence s y=1 := by
  unfold incidence
  rw [← pow_add,show rank s y+rank s y=2*rank s y by omega,pow_mul]
  simp
private theorem l6closed_14_single_link (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    link y (Finsupp.single s a) =
      if y∈s then a • Finsupp.single (s.erase y) (incidence s y) else 0 := by
  unfold link
  rw [Finsupp.sum_single_index (by split_ifs <;> simp)]
  rw [l6closed_14_nat_dEq]
private theorem l6closed_14_single_cone (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    cone y (Finsupp.single s a)=a • faceCone y s := by
  unfold cone
  rw [Finsupp.sum_single_index (by simp)]
private theorem l6closed_14_fresh_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∉s) :
    Fresh y (Finsupp.single s a) := by
  intro t ht
  have he := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  exact he ▸ hy
private theorem l6closed_14_link_cone (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) :
    l6closed_14_K y (l6closed_14_C y c)=c := by
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hys := hy s hs
  change link y (cone y (Finsupp.single s (c s))) = Finsupp.single s (c s)
  rw [l6closed_14_single_cone]
  unfold faceCone
  rw [l6closed_14_nat_dEq]
  rw [if_neg hys]
  change l6closed_14_K y (c s • Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [map_zsmul]
  change c s • link y (Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [l6closed_14_single_link,if_pos (Finset.mem_insert_self _ _),Finset.erase_insert hys,
    Finsupp.smul_single,smul_eq_mul,l6closed_14_incidence_sq]
  simp
private theorem l6closed_14_cone_link_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∈s) :
    cone y (link y (Finsupp.single s a))=Finsupp.single s a := by
  rw [l6closed_14_single_link,if_pos hy]
  change l6closed_14_C y (a • Finsupp.single (s.erase y) (incidence s y)) = _
  rw [map_zsmul]
  change a • cone y (Finsupp.single (s.erase y) (incidence s y)) = _
  rw [l6closed_14_single_cone]
  unfold faceCone
  rw [l6closed_14_nat_dEq]
  rw [if_neg (Finset.notMem_erase y s),Finset.insert_erase hy,
    Finsupp.smul_single,smul_eq_mul,l6closed_14_incidence_sq]
  simp
private theorem l6closed_14_link_fresh (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) : link y c=0 := by
  unfold link
  rw [l6closed_14_nat_dEq]
  apply Finset.sum_eq_zero
  intro s hs
  dsimp only
  rw [if_neg (hy s hs)]
private theorem l6closed_14_relabel_fresh (f : ℕ → ℕ) (hf : Function.Injective f)
    (c : Chain ℕ) (y : ℕ) (hy : Fresh y c) : Fresh (f y) (relabel f c) := by
  intro s hs hyin
  apply Finsupp.mem_support_iff.mp hs
  unfold relabel
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  change (c t • listedFace (f ∘ t.orderEmbOfFin rfl)) s=0
  rw [Finsupp.smul_apply]
  unfold listedFace
  rw [l6closed_14_nat_dEq]
  rw [Finsupp.single_apply]
  split_ifs with he
  · exfalso
    have hfy : f y ∈ Finset.univ.image (f ∘ t.orderEmbOfFin rfl) := he.symm ▸ hyin
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hfy
    exact hy t ht ((hf hi) ▸ t.orderEmbOfFin_mem rfl i)
  · simp
private theorem l6closed_14_single_natural (f : ℕ → ℕ) (hf : Function.Injective f)
    (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    l6closed_14_L f (l6closed_14_K y (Finsupp.single s a)) = l6closed_14_K (f y) (l6closed_14_L f (Finsupp.single s a)) := by
  by_cases hy : y∈s
  · have hbase : Fresh y (link y (Finsupp.single s a)) := PLDegree.link_chain_algebra.2.1 _ _
    have hc := l6closed_14_cone_link_single s a y hy
    change relabel f (link y (Finsupp.single s a)) =
      link (f y) (relabel f (Finsupp.single s a))
    conv_rhs => rw [← hc]
    rw [Sierksma.l6_relabel_cone f hf]
    exact (l6closed_14_link_cone (f y) _ (l6closed_14_relabel_fresh f hf _ y hbase)).symm
  · change relabel f (link y (Finsupp.single s a)) =
      link (f y) (relabel f (Finsupp.single s a))
    rw [l6closed_14_link_fresh y _ (l6closed_14_fresh_single s a y hy),
      l6closed_14_link_fresh (f y) _ (l6closed_14_relabel_fresh f hf _ y (l6closed_14_fresh_single s a y hy))]
    simp [relabel]
theorem Sierksma.l6_relabel_link (f : ℕ → ℕ) (hf : Function.Injective f)
    (y : ℕ) (c : Chain ℕ) :
    relabel f (link y c)=link (f y) (relabel f c)  := by
  change l6closed_14_L f (l6closed_14_K y c)=l6closed_14_K (f y) (l6closed_14_L f c)
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact l6closed_14_single_natural f hf s (c s) y
end
end

section
open PLDegree Sierksma
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private def l6closed_15_C (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private def l6closed_15_L (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := relabel f
  map_zero' := by simp [relabel]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private theorem l6closed_15_inc_list (s : Finset ℕ) :
    listedFace (s.orderEmbOfFin rfl) = Finsupp.single s 1 := by
  unfold listedFace
  have him : Finset.univ.image (s.orderEmbOfFin rfl) = s := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact s.orderEmbOfFin_mem rfl i
    · intro hv
      exact ⟨(s.orderIsoOfFin rfl).symm ⟨v,hv⟩, by simp [Finset.orderEmbOfFin]⟩
  congr 1
  · convert him using 1 <;> ext v <;> simp only [Finset.mem_image]
  · unfold listSign
    have hf : (Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij h
      exact (not_lt_of_ge ((s.orderEmbOfFin rfl).strictMono (Finset.mem_filter.mp h).2.1).le)
        (Finset.mem_filter.mp h).2.2
    calc
      _ = (-1 : ℤ)^((Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1)).card) := by
        congr 2
        ext ij
        simp only [Finset.mem_filter]
      _ = 1 := by rw [hf]; simp

private theorem l6closed_15_gp_relabel (f : ℕ → ℕ) (hf : Function.Injective f)
    (F : ℕ → W8) (c : Chain ℕ) (hgp : ChainGP (F ∘ f) c) : ChainGP F (relabel f c) := by
  intro s hs
  by_contra hn
  apply Finsupp.mem_support_iff.mp hs
  unfold relabel
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  change (c t • listedFace (f ∘ t.orderEmbOfFin rfl)) s=0
  rw [Finsupp.smul_apply]
  unfold listedFace
  have him : Finset.univ.image (f ∘ t.orderEmbOfFin rfl)=t.image f := by
    rw [← Finset.image_image,Finset.image_orderEmbOfFin_univ]
  have hneq : Finset.univ.image (f ∘ t.orderEmbOfFin rfl)≠s := by
    intro heq
    apply hn
    rw [← heq,him]
    exact (Sierksma.l6_gp_image f hf F t).mpr (hgp t ht)
  rw [Finsupp.single_apply]
  split_ifs with heq
  · apply False.elim
    apply hneq
    ext v
    rw [← heq]
    simp only [Finset.mem_image]
  · simp
private theorem l6closed_15_fixes_chain (f : ℕ → ℕ) (hf : Function.Injective f) (c : Chain ℕ)
    (h : ∀ s ∈ c.support, ∀ v ∈ s, f v=v) : relabel f c=c := by
  change l6closed_15_L f c=c
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : Finsupp.single s (c s)=c s • Finsupp.single s 1 := by simp
  rw [hs',map_zsmul]
  congr 1
  change relabel f (Finsupp.single s 1)=Finsupp.single s 1
  rw [← l6closed_15_inc_list,PLDegree.relabel_listed_face _ (s.orderEmbOfFin rfl).injective f hf]
  congr 1
  funext i
  exact h s hs _ (s.orderEmbOfFin_mem rfl i)
private theorem l6closed_15_hex_fresh (v : ℕ) (hv : 24 ≤ v) : Fresh v HexCycle := by
  intro s hs hmem
  have hlt := (Sierksma.hexagon_join_cycle.2.2.2 s hs v hmem).1
  omega
private theorem l6closed_15_swap_hex (p : ℕ) (hp : 24≤p) :
    relabel (Equiv.swap p 27) HexCycle=HexCycle := by
  apply l6closed_15_fixes_chain _ (Equiv.swap p 27).injective
  intro s hs v hv
  have hb := (Sierksma.hexagon_join_cycle.2.2.2 s hs v hv).1
  exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
private theorem l6closed_15_hex_maps (x y : EngineParams)
    (hm : ∀ i : Fin 9, i≠8 → x i=y i) (v : ℕ) (hv : v<24) :
    EngineMap x v=EngineMap y v := by
  simp only [EngineMap,dif_pos hv]
  rw [hm ⟨2*(v/6)+v%2,by omega⟩ (by apply Fin.ne_of_val_ne; simp; omega)]
theorem Sierksma.l6_apex_move_count (x y : EngineParams)
    (hx : EngineGeneric x) (hy : EngineGeneric y)
    (hm : ∀ i : Fin 9, i ≠ 8 → x i=y i) :
    ∀ j : Fin 3, ConeCount x j=ConeCount y j  := by
  intro j
  let p := 24+j.val
  let σ : Equiv.Perm ℕ := Equiv.swap p 27
  let G : ℕ → W8 := fun v => if v=27 then EngineMap y p else EngineMap x v
  have hp : 24≤p ∧ p<27 := by dsimp [p]; omega
  have hσz : relabel σ HexCycle=HexCycle := l6closed_15_swap_hex p hp.1
  have hcone : relabel σ (cone p HexCycle)=cone 27 HexCycle := by
    rw [Sierksma.l6_relabel_cone _ σ.injective,hσz]
    simp [σ]
  have hGx : ∀ s ∈ (cone p HexCycle).support, ∀ v ∈ s, G v=EngineMap x v := by
    intro s hs v hv
    obtain ⟨t,ht,hpt,rfl⟩ := Sierksma.l6_chain_support_tools.2.2 _ _ _ hs
    obtain rfl | hv := Finset.mem_insert.mp hv
    · simp [G,show p≠27 by omega]
    · have hb := (Sierksma.hexagon_join_cycle.2.2.2 t ht v hv).1
      simp [G,show v≠27 by omega]
  have hGy : ∀ s ∈ (cone p HexCycle).support, ∀ v ∈ s,
      (G ∘ σ) v=EngineMap y v := by
    intro s hs v hv
    obtain ⟨t,ht,hpt,rfl⟩ := Sierksma.l6_chain_support_tools.2.2 _ _ _ hs
    obtain rfl | hv := Finset.mem_insert.mp hv
    · simp [G,σ,Function.comp_apply]
    · have hb := (Sierksma.hexagon_join_cycle.2.2.2 t ht v hv).1
      rw [Function.comp_apply,show σ v=v from Equiv.swap_apply_of_ne_of_ne
        (by omega) (by omega)]
      simp only [G,if_neg (show v≠27 by omega)]
      exact l6closed_15_hex_maps x y hm v hb
  have hgp : ChainGP G (cone p HexCycle) :=
    (Sierksma.l6_chain_support_tools.2.1 _ _ _ hGx).2.mpr (hx j)
  have hg' : ChainGP G (cone 27 HexCycle) := by
    rw [← hcone]
    apply l6closed_15_gp_relabel σ σ.injective G
    exact (Sierksma.l6_chain_support_tools.2.1 _ _ _ hGy).2.mpr (hy j)
  have heq := PLDegree.apex_independence (by norm_num : 1≤8) G HexCycle p 27
    Sierksma.hexagon_join_cycle.1 Sierksma.hexagon_join_cycle.2.1
    (l6closed_15_hex_fresh p hp.1) (l6closed_15_hex_fresh 27 (by norm_num)) hgp hg'
  have hrel := PLDegree.signed_count_relabel σ σ.injective G (cone p HexCycle)
  rw [hcone] at hrel
  rw [(Sierksma.l6_chain_support_tools.2.1 _ _ _ hGx).1,
    hrel,(Sierksma.l6_chain_support_tools.2.1 _ _ _ hGy).1] at heq
  exact heq
end
end

section
open PLDegree Sierksma
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
private def l6closed_16_C (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
theorem Sierksma.l6_three_bubble_count
    (F : ℕ → W8) (z : Chain ℕ) (old new : Fin 3 → ℕ) (s : ℕ)
    (hc : IsCycle z) (hnew : ∀ i, Fresh (new i) z) (hne : ∀ i, new i≠old i)
    (hs : Fresh s z)
    (z' : Chain ℕ)
    (hz' : z' = z - (∑ i : Fin 3, cone (old i) (link (old i) z)) +
      (∑ i : Fin 3, cone (new i) (link (old i) z)))
    (hs' : Fresh s z')
    (hg : ChainGP F (cone s z)) (hg' : ChainGP F (cone s z'))
    (hgb : ∀ i : Fin 3, ChainGP F (bubble (old i) (new i) z))
    (f : ℕ → ℕ) (hf : Function.Injective f) (hz : relabel f z=z)
    (ho : ∀ i : Fin 3, f (old i)=old (finRotate 3 i))
    (hn : ∀ i : Fin 3, f (new i)=new (finRotate 3 i))
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : 0<A.det)
    (hF : ∀ v, F (f v)=A.mulVec (F v)) :
    signedCount F (cone s z)-signedCount F (cone s z') =
      3*signedCount F (bubble (old 0) (new 0) z)  := by
  let B : Fin 3 → Chain ℕ := fun i => bubble (old i) (new i) z
  have hb : ∀ i, boundary (B i) = cone (old i) (link (old i) z)-cone (new i) (link (old i) z) := by
    intro i
    have hh := (PLDegree.link_move_boundary z (old i) (new i) hc (hnew i) (hne i)).2.2.1
    dsimp [B]
    rw [hh,moveVertex]
    abel
  have hboundary : boundary (∑ i : Fin 3, B i)=z-z' := by
    change BoundaryOperator (∑ i : Fin 3, B i)=z-z'
    rw [map_sum]
    change (∑ i : Fin 3, boundary (B i))=z-z'
    simp_rw [hb]
    rw [Finset.sum_sub_distrib,hz']
    abel
  have hmcy : IsCycle z' := by
    have hlinks : ∀ i : Fin 3, IsCycle (link (old i) z) := fun i =>
      (PLDegree.link_move_boundary z (old i) (new i) hc (hnew i) (hne i)).1
    have hstar : ∀ i : Fin 3,
        boundary (cone (old i) (link (old i) z))=link (old i) z ∧
        boundary (cone (new i) (link (old i) z))=link (old i) z := by
      intro i
      obtain ⟨hell,hm,hbb,hfresh⟩ := PLDegree.link_move_boundary z (old i) (new i) hc (hnew i) (hne i)
      have hoFresh := PLDegree.link_chain_algebra.2.1 (old i) z
      have hnFresh := PLDegree.link_chain_algebra.2.2.1 (old i) (new i) z (hnew i)
      constructor
      all_goals
        rw [PLDegree.cone_boundary _ _ (by assumption)]
        change _ - cone _ (boundary (link (old i) z)) = _
        rw [hlinks i]
        simp [cone]
    change BoundaryOperator z'=0
    rw [hz',map_add,map_sub,map_sum,map_sum]
    change boundary z-(∑ i : Fin 3, boundary (cone (old i) (link (old i) z)))+
      (∑ i : Fin 3, boundary (cone (new i) (link (old i) z)))=0
    rw [hc]
    simp_rw [(hstar _).1,(hstar _).2]
    abel
  have hcy : IsCycle (cone s z-cone s z'-(∑ i : Fin 3,B i)) := by
    change BoundaryOperator (cone s z-cone s z'-(∑ i : Fin 3,B i))=0
    rw [map_sub,map_sub]
    change boundary (cone s z)-boundary (cone s z')-boundary (∑ i : Fin 3,B i)=0
    rw [PLDegree.cone_boundary s z hs,PLDegree.cone_boundary s z' hs',
      hc,hmcy,hboundary]
    simp [cone]
  have hgp : ChainGP F (cone s z-cone s z'-(∑ i : Fin 3,B i)) := by
    intro t ht
    by_contra hnGP
    have hzero (c : Chain ℕ) (hg : ChainGP F c) : c t=0 := by
      by_contra hn
      exact hnGP (hg t (Finsupp.mem_support_iff.mpr hn))
    have hbzero : (∑ i : Fin 3,B i) t=0 := by
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i _
      exact hzero (B i) (hgb i)
    have hnz := Finsupp.mem_support_iff.mp ht
    apply hnz
    simp only [Finsupp.sub_apply,hzero _ hg,hzero _ hg',hbzero,sub_self]
  have hzCount := PLDegree.cycle_degree_zero (by norm_num : 1≤8) F
    (cone s z-cone s z'-(∑ i : Fin 3,B i)) hcy hgp
  have hcount : signedCount F (cone s z)-signedCount F (cone s z') =
      ∑ i : Fin 3,signedCount F (B i) := by
    change PairingOperator (simplexDegree F)
      (cone s z-cone s z'-(∑ i : Fin 3,B i))=0 at hzCount
    rw [map_sub,map_sub,map_sum] at hzCount
    exact sub_eq_zero.mp hzCount
  have hrel : ∀ i : Fin 3, relabel f (B i)=B (finRotate 3 i) := by
    intro i
    dsimp [B,bubble]
    rw [Sierksma.l6_relabel_cone f hf,Sierksma.l6_relabel_cone f hf,
      Sierksma.l6_relabel_link f hf,hz,ho,hn]
  have hrot : ∀ i : Fin 3, signedCount F (B (finRotate 3 i))=signedCount F (B i) := by
    intro i
    rw [← hrel i,PLDegree.signed_count_relabel f hf]
    have heq : F ∘ f = fun v => A.mulVec (F v) := funext hF
    rw [heq]
    exact (PLDegree.positive_linear_degree_invariant A hA F).2 _
  have h1 : signedCount F (B 1)=signedCount F (B 0) := hrot 0
  have h2 : signedCount F (B 2)=signedCount F (B 0) := (hrot 1).trans h1
  rw [hcount]
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  change signedCount F (B 0)+(signedCount F (B 1)+signedCount F (B 2))=3*signedCount F (B 0)
  rw [h1,h2]
  ring
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
set_option maxHeartbeats 1000000
private theorem l6closed_17_old_lt (r : Fin 8) (i : Fin 3) : L6Old r i<24 := by
  dsimp [L6Old]
  omega
private theorem l6closed_17_shift_lt (v : ℕ) (h : v<27) : ShiftVertex v<27 := by
  unfold ShiftVertex
  split_ifs <;> omega
private theorem l6closed_17_shift_lt24 (v : ℕ) (h : v<24) : ShiftVertex v<24 := by
  unfold ShiftVertex
  rw [if_pos h]
  omega
private theorem l6closed_17_fresh_shift (v : ℕ) (hv : 27≤v) (hv' : v<51) :
    27≤L6Shift v ∧ L6Shift v<51 := by
  rw [L6Shift,if_neg (by omega),if_pos hv']
  have h := l6closed_17_shift_lt24 (v-27) (by omega)
  omega
private theorem l6closed_17_old_shift (v : ℕ) (hv : v<27) : L6Shift v=ShiftVertex v := by
  rw [L6Shift,if_pos hv]
private theorem l6closed_17_cubic : ∀ v : ℕ, L6Shift (L6Shift (L6Shift v))=v := by
  intro v
  by_cases h : v<27
  · rw [l6closed_17_old_shift v h,l6closed_17_old_shift _ (l6closed_17_shift_lt v h),
      l6closed_17_old_shift _ (l6closed_17_shift_lt _ (l6closed_17_shift_lt v h)),Sierksma.engine_shift_equivariance.1]
  · by_cases h' : v<51
    · have ha := l6closed_17_fresh_shift v (by omega) h'
      have hb := l6closed_17_fresh_shift (L6Shift v) ha.1 ha.2
      rw [L6Shift,if_neg (by omega),if_pos hb.2]
      simp only [L6Shift,if_neg (by omega : ¬v<27),if_pos h',
        if_neg (by omega : ¬L6Shift v<27),if_pos ha.2]
      have hz := l6closed_17_shift_lt24 (v-27) (by omega)
      simp only [show ¬27+ShiftVertex (v-27)<27 by omega,
        show 27+ShiftVertex (v-27)<51 by omega,ite_false,ite_true,
        Nat.add_sub_cancel_left]
      rw [Sierksma.engine_shift_equivariance.1]
      omega
    · have he : L6Shift v=v := by simp [L6Shift,h,h']
      rw [he,he,he]
private theorem l6closed_17_bounds : ∀ r : Fin 8, ∀ i : Fin 3,
    L6Old r i<24 ∧ 27≤L6New r i ∧ L6New r i<51 := by
  intro r i
  have h := l6closed_17_old_lt r i
  dsimp [L6New]
  omega
private theorem l6closed_17_old_inj (r : Fin 8) : Function.Injective (L6Old r) := by
  intro i j hij
  apply Fin.ext
  dsimp [L6Old] at hij
  omega
private theorem l6closed_17_swap_old (r : Fin 8) (i : Fin 3) : L6Swap r (L6Old r i)=L6New r i := by
  fin_cases r <;> fin_cases i <;> norm_num [L6Swap,L6Old,L6New,Equiv.swap_apply_def]
private theorem l6closed_17_swap_fix (r : Fin 8) (v : ℕ)
    (h : ∀ i : Fin 3, v≠L6Old r i ∧ v≠L6New r i) : L6Swap r v=v := by
  simp only [L6Swap,Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (h 0).1 (h 0).2,
    Equiv.swap_apply_of_ne_of_ne (h 1).1 (h 1).2,
    Equiv.swap_apply_of_ne_of_ne (h 2).1 (h 2).2]
private theorem l6closed_17_orbit_shift (r : Fin 8) (i : Fin 3) :
    L6Shift (L6Old r i)=L6Old r (finRotate 3 i) ∧
      L6Shift (L6New r i)=L6New r (finRotate 3 i) := by
  have ho := l6closed_17_old_lt r i
  have hn := l6closed_17_bounds r i
  rw [l6closed_17_old_shift _ (by omega)]
  have hs : ShiftVertex (L6Old r i)=L6Old r (finRotate 3 i) := by
    fin_cases r <;> fin_cases i <;> norm_num [ShiftVertex,L6Old,Fin.val_add]
  refine ⟨hs,?_⟩
  rw [L6Shift,if_neg (by omega),if_pos hn.2.2]
  simp only [L6New,Nat.add_sub_cancel_left,hs]
private theorem l6closed_17_equivariant (x y : EngineParams) (v : ℕ) :
    L6Map x y (L6Shift v)=R8 (L6Map x y v) := by
  by_cases h : v<27
  · rw [l6closed_17_old_shift v h]
    simp only [L6Map,if_pos h,if_pos (l6closed_17_shift_lt v h)]
    exact Sierksma.engine_shift_equivariance.2.2 x v
  · by_cases h' : v<51
    · have hs := l6closed_17_fresh_shift v (by omega) h'
      simp only [L6Map,if_neg h,if_pos h',if_neg (by omega : ¬L6Shift v<27),if_pos hs.2]
      rw [L6Shift,if_neg h,if_pos h',Nat.add_sub_cancel_left]
      exact Sierksma.engine_shift_equivariance.2.2 y (v-27)
    · have hs : L6Shift v=v := by simp [L6Shift,h,h']
      simp only [hs,L6Map,if_neg h,if_neg h']
      funext j
      unfold R8
      split_ifs <;> simp
theorem Sierksma.l6_orbit_label_geometry :
    (∀ r : Fin 8, ∀ i : Fin 3, L6Old r i<24 ∧ 27≤L6New r i ∧ L6New r i<51) ∧
    (∀ r : Fin 8, Function.Injective (L6Old r)) ∧
    (∀ r : Fin 8, ∀ i : Fin 3, L6Swap r (L6Old r i)=L6New r i) ∧
    (∀ r : Fin 8, ∀ v : ℕ, (∀ i : Fin 3, v≠L6Old r i ∧ v≠L6New r i) → L6Swap r v=v) ∧
    (Function.Injective L6Shift ∧ (∀ v : ℕ, L6Shift (L6Shift (L6Shift v))=v)) ∧
    (∀ r : Fin 8, ∀ i : Fin 3, L6Shift (L6Old r i)=L6Old r (finRotate 3 i) ∧
      L6Shift (L6New r i)=L6New r (finRotate 3 i)) ∧
    (∀ x y : EngineParams, ∀ v : ℕ, L6Map x y (L6Shift v)=R8 (L6Map x y v))  := by
  refine ⟨l6closed_17_bounds,l6closed_17_old_inj,l6closed_17_swap_old,l6closed_17_swap_fix,⟨?_,l6closed_17_cubic⟩,l6closed_17_orbit_shift,l6closed_17_equivariant⟩
  intro a b hab
  have h := congrArg (fun v => L6Shift (L6Shift v)) hab
  simpa only [l6closed_17_cubic] using h
end
end

section
open PLDegree Sierksma
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private def l6closed_18_C (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private def l6closed_18_L (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := relabel f
  map_zero' := by simp [relabel]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private theorem l6closed_18_inc_list (s : Finset ℕ) :
    listedFace (s.orderEmbOfFin rfl) = Finsupp.single s 1 := by
  unfold listedFace
  have him : Finset.univ.image (s.orderEmbOfFin rfl) = s := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact s.orderEmbOfFin_mem rfl i
    · intro hv
      exact ⟨(s.orderIsoOfFin rfl).symm ⟨v,hv⟩, by simp [Finset.orderEmbOfFin]⟩
  congr 1
  · convert him using 1 <;> ext v <;> simp only [Finset.mem_image]
  · unfold listSign
    have hf : (Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij h
      exact (not_lt_of_ge ((s.orderEmbOfFin rfl).strictMono (Finset.mem_filter.mp h).2.1).le)
        (Finset.mem_filter.mp h).2.2
    calc
      _ = (-1 : ℤ)^((Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1)).card) := by
        congr 2
        ext ij
        simp only [Finset.mem_filter]
      _ = 1 := by rw [hf]; simp

private theorem l6closed_18_nat_dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq ℕ)=instDecidableEqNat :=
  Subsingleton.elim _ _
private def l6closed_18_K (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := link y
  map_zero' := by simp [link]
  map_add' a b := Finsupp.sum_add_index'
    (fun _ => by split_ifs <;> simp) (fun _ _ _ => by split_ifs <;> simp [add_smul])
private theorem l6closed_18_incidence_sq (s : Finset ℕ) (y : ℕ) : incidence s y * incidence s y=1 := by
  unfold incidence
  rw [← pow_add,show rank s y+rank s y=2*rank s y by omega,pow_mul]
  simp
private theorem l6closed_18_single_link (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    link y (Finsupp.single s a) =
      if y∈s then a • Finsupp.single (s.erase y) (incidence s y) else 0 := by
  unfold link
  rw [Finsupp.sum_single_index (by split_ifs <;> simp)]
  rw [l6closed_18_nat_dEq]
private theorem l6closed_18_single_cone (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    cone y (Finsupp.single s a)=a • faceCone y s := by
  unfold cone
  rw [Finsupp.sum_single_index (by simp)]
private theorem l6closed_18_fresh_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∉s) :
    Fresh y (Finsupp.single s a) := by
  intro t ht
  have he := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  exact he ▸ hy
private theorem l6closed_18_link_cone (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) :
    l6closed_18_K y (l6closed_18_C y c)=c := by
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hys := hy s hs
  change link y (cone y (Finsupp.single s (c s))) = Finsupp.single s (c s)
  rw [l6closed_18_single_cone]
  unfold faceCone
  rw [l6closed_18_nat_dEq]
  rw [if_neg hys]
  change l6closed_18_K y (c s • Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [map_zsmul]
  change c s • link y (Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [l6closed_18_single_link,if_pos (Finset.mem_insert_self _ _),Finset.erase_insert hys,
    Finsupp.smul_single,smul_eq_mul,l6closed_18_incidence_sq]
  simp
private theorem l6closed_18_cone_link_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∈s) :
    cone y (link y (Finsupp.single s a))=Finsupp.single s a := by
  rw [l6closed_18_single_link,if_pos hy]
  change l6closed_18_C y (a • Finsupp.single (s.erase y) (incidence s y)) = _
  rw [map_zsmul]
  change a • cone y (Finsupp.single (s.erase y) (incidence s y)) = _
  rw [l6closed_18_single_cone]
  unfold faceCone
  rw [l6closed_18_nat_dEq]
  rw [if_neg (Finset.notMem_erase y s),Finset.insert_erase hy,
    Finsupp.smul_single,smul_eq_mul,l6closed_18_incidence_sq]
  simp
private theorem l6closed_18_link_fresh (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) : link y c=0 := by
  unfold link
  rw [l6closed_18_nat_dEq]
  apply Finset.sum_eq_zero
  intro s hs
  dsimp only
  rw [if_neg (hy s hs)]
private theorem l6closed_18_relabel_fresh (f : ℕ → ℕ) (hf : Function.Injective f)
    (c : Chain ℕ) (y : ℕ) (hy : Fresh y c) : Fresh (f y) (relabel f c) := by
  intro s hs hyin
  apply Finsupp.mem_support_iff.mp hs
  unfold relabel
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  change (c t • listedFace (f ∘ t.orderEmbOfFin rfl)) s=0
  rw [Finsupp.smul_apply]
  unfold listedFace
  rw [l6closed_18_nat_dEq]
  rw [Finsupp.single_apply]
  split_ifs with he
  · exfalso
    have hfy : f y ∈ Finset.univ.image (f ∘ t.orderEmbOfFin rfl) := he.symm ▸ hyin
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hfy
    exact hy t ht ((hf hi) ▸ t.orderEmbOfFin_mem rfl i)
  · simp
private theorem l6closed_18_fixes_chain (f : ℕ → ℕ) (hf : Function.Injective f) (c : Chain ℕ)
    (h : ∀ s ∈ c.support, ∀ v ∈ s, f v=v) : relabel f c=c := by
  change l6closed_18_L f c=c
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : Finsupp.single s (c s)=c s • Finsupp.single s 1 := by simp
  rw [hs',map_zsmul]
  congr 1
  change relabel f (Finsupp.single s 1)=Finsupp.single s 1
  rw [← l6closed_18_inc_list,PLDegree.relabel_listed_face _ (s.orderEmbOfFin rfl).injective f hf]
  congr 1
  funext i
  exact h s hs _ (s.orderEmbOfFin_mem rfl i)

private theorem l6closed_18_old_shift (r : Fin 8) (i : Fin 3) :
    ShiftVertex (L6Old r i)=L6Old r (finRotate 3 i) := by
  have H := (Sierksma.l6_orbit_label_geometry.2.2.2.2.2.1 r i).1
  rw [L6Shift,if_pos (by have h := (Sierksma.l6_orbit_label_geometry.1 r i).1; omega)] at H
  exact H
private theorem l6closed_18_other_old_notmem (r : Fin 8) (s : Finset ℕ) (hs : s∈HexCycle.support)
    (k : Fin 3) (hk : L6Old r k∈s) : ∀ i : Fin 3, i≠k → L6Old r i∉s := by
  intro i hik
  have hcases : i=finRotate 3 k ∨ i=finRotate 3 (finRotate 3 k) := by
    fin_cases i <;> fin_cases k <;> simp_all [Fin.val_add]
  have h := Sierksma.hexagon_join_cycle.2.2.2 s hs (L6Old r k) hk
  rcases hcases with hi | hi
  · rw [hi,← l6closed_18_old_shift]
    exact h.2.1
  · rw [hi,← l6closed_18_old_shift,← l6closed_18_old_shift]
    exact h.2.2
private theorem l6closed_18_single_fixed (f : ℕ → ℕ) (hf : Function.Injective f)
    (s : Finset ℕ) (a : ℤ) (h : ∀ v∈s, f v=v) : relabel f (Finsupp.single s a)=Finsupp.single s a := by
  apply l6closed_18_fixes_chain f hf
  intro t ht v hv
  have he := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  exact h v (he ▸ hv)
private theorem l6closed_18_replace_single (r : Fin 8) (s : Finset ℕ) (hs : s∈HexCycle.support) (a : ℤ) :
    relabel (L6Swap r) (Finsupp.single s a) = Finsupp.single s a -
      (∑ i : Fin 3, cone (L6Old r i) (link (L6Old r i) (Finsupp.single s a))) +
      (∑ i : Fin 3, cone (L6New r i) (link (L6Old r i) (Finsupp.single s a))) := by
  have hb : ∀ v∈s, v<24 := fun v hv => (Sierksma.hexagon_join_cycle.2.2.2 s hs v hv).1
  by_cases h : ∃ k : Fin 3,L6Old r k∈s
  · obtain ⟨k,hk⟩ := h
    have hno := l6closed_18_other_old_notmem r s hs k hk
    have hsum (p : Fin 3 → ℕ) :
        (∑ i : Fin 3, cone (p i) (link (L6Old r i) (Finsupp.single s a))) =
          cone (p k) (link (L6Old r k) (Finsupp.single s a)) := by
      apply Finset.sum_eq_single k
      · intro i _ hik
        rw [l6closed_18_link_fresh _ _ (l6closed_18_fresh_single s a _ (hno i hik))]
        simp [cone]
      · simp
    rw [hsum (L6Old r),hsum (L6New r),l6closed_18_cone_link_single s a (L6Old r k) hk]
    simp only [sub_self,zero_add]
    have hf : ∀ v∈s.erase (L6Old r k), L6Swap r v=v := by
      intro v hv
      apply Sierksma.l6_orbit_label_geometry.2.2.2.1
      intro i
      refine ⟨?_,?_⟩
      · by_cases hi : i=k
        · subst i
          exact (Finset.mem_erase.mp hv).1
        · intro he
          exact hno i hi (he ▸ Finset.mem_of_mem_erase hv)
      · have hn := (Sierksma.l6_orbit_label_geometry.1 r i).2.1
        have hv' := hb v (Finset.mem_of_mem_erase hv)
        omega
    have hc := l6closed_18_cone_link_single s a (L6Old r k) hk
    conv_lhs => rw [← hc]
    rw [Sierksma.l6_relabel_cone _ (L6Swap r).injective,
      Sierksma.l6_orbit_label_geometry.2.2.1]
    congr 1
    rw [l6closed_18_single_link,if_pos hk]
    change l6closed_18_L (L6Swap r) (a • Finsupp.single (s.erase (L6Old r k)) (incidence s (L6Old r k))) = _
    rw [map_zsmul]
    change a • relabel (L6Swap r) (Finsupp.single (s.erase (L6Old r k)) (incidence s (L6Old r k))) = _
    rw [l6closed_18_single_fixed _ (L6Swap r).injective _ _ hf]
  · have hn : ∀ i : Fin 3,L6Old r i∉s := by simpa using h
    have hz : ∀ i : Fin 3, link (L6Old r i) (Finsupp.single s a)=0 := fun i =>
      l6closed_18_link_fresh _ _ (l6closed_18_fresh_single s a _ (hn i))
    simp_rw [hz]
    simp only [cone,Finsupp.sum_zero_index,Finset.sum_const_zero,sub_zero,add_zero]
    apply l6closed_18_single_fixed _ (L6Swap r).injective
    intro v hv
    apply Sierksma.l6_orbit_label_geometry.2.2.2.1
    intro i
    refine ⟨fun he => hn i (he ▸ hv),?_⟩
    have hv' := hb v hv
    have hn' := (Sierksma.l6_orbit_label_geometry.1 r i).2.1
    omega
theorem Sierksma.l6_replacement_identity (r : Fin 8) :
    L6Replaced r = HexCycle - (∑ i : Fin 3, cone (L6Old r i) (link (L6Old r i) HexCycle)) +
      (∑ i : Fin 3, cone (L6New r i) (link (L6Old r i) HexCycle))  := by
  let D : Chain ℕ →+ Chain ℕ := AddMonoidHom.id _ -
    (∑ i : Fin 3,(l6closed_18_C (L6Old r i)).comp (l6closed_18_K (L6Old r i))) +
    (∑ i : Fin 3,(l6closed_18_C (L6New r i)).comp (l6closed_18_K (L6Old r i)))
  have hD (c : Chain ℕ) : D c = c - (∑ i : Fin 3,cone (L6Old r i) (link (L6Old r i) c)) +
      (∑ i : Fin 3,cone (L6New r i) (link (L6Old r i) c)) := by
    simp only [D,AddMonoidHom.add_apply,AddMonoidHom.sub_apply,AddMonoidHom.id_apply,
      AddMonoidHom.finset_sum_apply,AddMonoidHom.comp_apply]
    rfl
  rw [← hD]
  change l6closed_18_L (L6Swap r) HexCycle = D HexCycle
  rw [← Finsupp.sum_single HexCycle]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hD]
  exact l6closed_18_replace_single r s hs (HexCycle s)
end
end

section
open PLDegree Sierksma
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private def l6closed_19_C (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private def l6closed_19_L (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := relabel f
  map_zero' := by simp [relabel]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private theorem l6closed_19_inc_list (s : Finset ℕ) :
    listedFace (s.orderEmbOfFin rfl) = Finsupp.single s 1 := by
  unfold listedFace
  have him : Finset.univ.image (s.orderEmbOfFin rfl) = s := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact s.orderEmbOfFin_mem rfl i
    · intro hv
      exact ⟨(s.orderIsoOfFin rfl).symm ⟨v,hv⟩, by simp [Finset.orderEmbOfFin]⟩
  congr 1
  · convert him using 1 <;> ext v <;> simp only [Finset.mem_image]
  · unfold listSign
    have hf : (Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij h
      exact (not_lt_of_ge ((s.orderEmbOfFin rfl).strictMono (Finset.mem_filter.mp h).2.1).le)
        (Finset.mem_filter.mp h).2.2
    calc
      _ = (-1 : ℤ)^((Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1)).card) := by
        congr 2
        ext ij
        simp only [Finset.mem_filter]
      _ = 1 := by rw [hf]; simp

private theorem l6closed_19_nat_dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq ℕ)=instDecidableEqNat :=
  Subsingleton.elim _ _
private def l6closed_19_K (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := link y
  map_zero' := by simp [link]
  map_add' a b := Finsupp.sum_add_index'
    (fun _ => by split_ifs <;> simp) (fun _ _ _ => by split_ifs <;> simp [add_smul])
private theorem l6closed_19_incidence_sq (s : Finset ℕ) (y : ℕ) : incidence s y * incidence s y=1 := by
  unfold incidence
  rw [← pow_add,show rank s y+rank s y=2*rank s y by omega,pow_mul]
  simp
private theorem l6closed_19_single_link (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    link y (Finsupp.single s a) =
      if y∈s then a • Finsupp.single (s.erase y) (incidence s y) else 0 := by
  unfold link
  rw [Finsupp.sum_single_index (by split_ifs <;> simp)]
  rw [l6closed_19_nat_dEq]
private theorem l6closed_19_single_cone (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    cone y (Finsupp.single s a)=a • faceCone y s := by
  unfold cone
  rw [Finsupp.sum_single_index (by simp)]
private theorem l6closed_19_fresh_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∉s) :
    Fresh y (Finsupp.single s a) := by
  intro t ht
  have he := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  exact he ▸ hy
private theorem l6closed_19_link_cone (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) :
    l6closed_19_K y (l6closed_19_C y c)=c := by
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hys := hy s hs
  change link y (cone y (Finsupp.single s (c s))) = Finsupp.single s (c s)
  rw [l6closed_19_single_cone]
  unfold faceCone
  rw [l6closed_19_nat_dEq]
  rw [if_neg hys]
  change l6closed_19_K y (c s • Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [map_zsmul]
  change c s • link y (Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [l6closed_19_single_link,if_pos (Finset.mem_insert_self _ _),Finset.erase_insert hys,
    Finsupp.smul_single,smul_eq_mul,l6closed_19_incidence_sq]
  simp
private theorem l6closed_19_cone_link_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∈s) :
    cone y (link y (Finsupp.single s a))=Finsupp.single s a := by
  rw [l6closed_19_single_link,if_pos hy]
  change l6closed_19_C y (a • Finsupp.single (s.erase y) (incidence s y)) = _
  rw [map_zsmul]
  change a • cone y (Finsupp.single (s.erase y) (incidence s y)) = _
  rw [l6closed_19_single_cone]
  unfold faceCone
  rw [l6closed_19_nat_dEq]
  rw [if_neg (Finset.notMem_erase y s),Finset.insert_erase hy,
    Finsupp.smul_single,smul_eq_mul,l6closed_19_incidence_sq]
  simp
private theorem l6closed_19_link_fresh (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) : link y c=0 := by
  unfold link
  rw [l6closed_19_nat_dEq]
  apply Finset.sum_eq_zero
  intro s hs
  dsimp only
  rw [if_neg (hy s hs)]
private theorem l6closed_19_relabel_fresh (f : ℕ → ℕ) (hf : Function.Injective f)
    (c : Chain ℕ) (y : ℕ) (hy : Fresh y c) : Fresh (f y) (relabel f c) := by
  intro s hs hyin
  apply Finsupp.mem_support_iff.mp hs
  unfold relabel
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  change (c t • listedFace (f ∘ t.orderEmbOfFin rfl)) s=0
  rw [Finsupp.smul_apply]
  unfold listedFace
  rw [l6closed_19_nat_dEq]
  rw [Finsupp.single_apply]
  split_ifs with he
  · exfalso
    have hfy : f y ∈ Finset.univ.image (f ∘ t.orderEmbOfFin rfl) := he.symm ▸ hyin
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hfy
    exact hy t ht ((hf hi) ▸ t.orderEmbOfFin_mem rfl i)
  · simp
private theorem l6closed_19_fixes_chain (f : ℕ → ℕ) (hf : Function.Injective f) (c : Chain ℕ)
    (h : ∀ s ∈ c.support, ∀ v ∈ s, f v=v) : relabel f c=c := by
  change l6closed_19_L f c=c
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : Finsupp.single s (c s)=c s • Finsupp.single s 1 := by simp
  rw [hs',map_zsmul]
  congr 1
  change relabel f (Finsupp.single s 1)=Finsupp.single s 1
  rw [← l6closed_19_inc_list,PLDegree.relabel_listed_face _ (s.orderEmbOfFin rfl).injective f hf]
  congr 1
  funext i
  exact h s hs _ (s.orderEmbOfFin_mem rfl i)

private theorem l6closed_19_gp_relabel (f : ℕ → ℕ) (hf : Function.Injective f)
    (F : ℕ → W8) (c : Chain ℕ) (hgp : ChainGP (F ∘ f) c) : ChainGP F (relabel f c) := by
  intro s hs
  by_contra hn
  apply Finsupp.mem_support_iff.mp hs
  unfold relabel
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  change (c t • listedFace (f ∘ t.orderEmbOfFin rfl)) s=0
  rw [Finsupp.smul_apply]
  unfold listedFace
  have him : Finset.univ.image (f ∘ t.orderEmbOfFin rfl)=t.image f := by
    rw [← Finset.image_image,Finset.image_orderEmbOfFin_univ]
  have hneq : Finset.univ.image (f ∘ t.orderEmbOfFin rfl)≠s := by
    intro heq
    apply hn
    rw [← heq,him]
    exact (Sierksma.l6_gp_image f hf F t).mpr (hgp t ht)
  rw [Finsupp.single_apply]
  split_ifs with heq
  · apply False.elim
    apply hneq
    ext v
    rw [← heq]
    simp only [Finset.mem_image]
  · simp

private theorem l6closed_19_hex_fresh (v : ℕ) (hv : 24≤v) : Fresh v HexCycle := by
  intro t ht hmem
  have hlt := (Sierksma.hexagon_join_cycle.2.2.2 t ht v hmem).1
  omega
private theorem l6closed_19_selector_old (v : ℕ) (hv : v<24) (r : Fin 8)
    (h : 2*(v/6)+v%2=r.val) : ∃ i : Fin 3,v=L6Old r i := by
  let i : Fin 3 := ⟨v%6/2,by omega⟩
  refine ⟨i,?_⟩
  dsimp [i,L6Old]
  have hr := r.isLt
  omega
private theorem l6closed_19_new_map (x y : EngineParams) (r : Fin 8)
    (hm : ∀ i : Fin 9, i≠r.castSucc → x i=y i) (v : ℕ) (hv : v<24) :
    L6Map x y (L6Swap r v)=EngineMap y v := by
  by_cases h : ∃ i : Fin 3,v=L6Old r i
  · obtain ⟨i,rfl⟩ := h
    rw [Sierksma.l6_orbit_label_geometry.2.2.1]
    have hn := (Sierksma.l6_orbit_label_geometry.1 r i).2
    unfold L6Map
    rw [if_neg (by omega : ¬L6New r i<27),if_pos hn.2]
    simp only [L6New,Nat.add_sub_cancel_left]
  · have hfix : L6Swap r v=v := by
      apply Sierksma.l6_orbit_label_geometry.2.2.2.1
      intro i
      refine ⟨fun he => h ⟨i,he⟩,?_⟩
      have hn := (Sierksma.l6_orbit_label_geometry.1 r i).2.1
      omega
    rw [hfix,L6Map,if_pos (by omega)]
    simp only [EngineMap,dif_pos hv]
    rw [hm ⟨2*(v/6)+v%2,by omega⟩]
    intro he
    apply h
    exact l6closed_19_selector_old v hv r (congrArg Fin.val he)
private theorem l6closed_19_shift_invariant : relabel L6Shift HexCycle=HexCycle := by
  calc
    _ = relabel ShiftVertex HexCycle := by
      unfold relabel
      apply Finsupp.sum_congr
      intro t ht
      congr 1
      congr 1
      funext i
      have hv := (Sierksma.hexagon_join_cycle.2.2.2 t ht _ (t.orderEmbOfFin_mem rfl i)).1
      rw [L6Shift,if_pos (by omega)]
    _ = _ := Sierksma.hexagon_join_cycle.2.2.1
theorem Sierksma.l6_generic_orbit_move_count (x y : EngineParams)
    (hx : EngineGeneric x) (hy : EngineGeneric y) (r : Fin 8)
    (hm : ∀ i : Fin 9, i≠r.castSucc → x i=y i)
    (hgb : ∀ i : Fin 3, ChainGP (L6Map x y) (bubble (L6Old r i) (L6New r i) HexCycle)) :
    ∀ j : Fin 3, ConeCount x j-ConeCount y j =
      3*signedCount (L6Map x y) (bubble (L6Old r 0) (L6New r 0) HexCycle)  := by
  intro j
  let p := 24+j.val
  have hp : 24≤p ∧ p<27 := by dsimp [p]; omega
  have hfix : L6Swap r p=p := by
    apply Sierksma.l6_orbit_label_geometry.2.2.2.1
    intro i
    have h := Sierksma.l6_orbit_label_geometry.1 r i
    constructor <;> omega
  have hcone : relabel (L6Swap r) (cone p HexCycle)=cone p (L6Replaced r) := by
    rw [Sierksma.l6_relabel_cone _ (L6Swap r).injective,hfix]
    rfl
  have hold : ∀ t ∈ (cone p HexCycle).support, ∀ v∈t,L6Map x y v=EngineMap x v := by
    intro t ht v hv
    obtain ⟨s,hs,_,rfl⟩ := Sierksma.l6_chain_support_tools.2.2 _ _ _ ht
    obtain rfl | hv := Finset.mem_insert.mp hv
    · exact if_pos hp.2
    · have hv' := (Sierksma.hexagon_join_cycle.2.2.2 s hs v hv).1
      exact if_pos (by omega)
  have hnew : ∀ t ∈ (cone p HexCycle).support, ∀ v∈t,
      (L6Map x y ∘ L6Swap r) v=EngineMap y v := by
    intro t ht v hv
    obtain ⟨s,hs,_,rfl⟩ := Sierksma.l6_chain_support_tools.2.2 _ _ _ ht
    obtain rfl | hv := Finset.mem_insert.mp hv
    · rw [Function.comp_apply,hfix,L6Map,if_pos hp.2]
      change EngineMap x p=EngineMap y p
      simp only [EngineMap,dif_neg (show ¬p<24 by omega),dif_pos hp.2]
      rw [hm 8]
      apply Fin.ne_of_val_ne
      simp only [Fin.val_castSucc,Fin.reduceFinMk]
      omega
    · exact l6closed_19_new_map x y r hm v (Sierksma.hexagon_join_cycle.2.2.2 s hs v hv).1
  have hg : ChainGP (L6Map x y) (cone p HexCycle) :=
    (Sierksma.l6_chain_support_tools.2.1 _ _ _ hold).2.mpr (hx j)
  have hg' : ChainGP (L6Map x y) (cone p (L6Replaced r)) := by
    rw [← hcone]
    apply l6closed_19_gp_relabel _ (L6Swap r).injective
    exact (Sierksma.l6_chain_support_tools.2.1 _ _ _ hnew).2.mpr (hy j)
  have hfresh : Fresh p (L6Replaced r) := by
    rw [L6Replaced,← hfix]
    exact l6closed_19_relabel_fresh _ (L6Swap r).injective _ _ (l6closed_19_hex_fresh p hp.1)
  obtain ⟨A,hA,hAv⟩ := Sierksma.R8_orientation_preserving.2
  have H := Sierksma.l6_three_bubble_count (L6Map x y) HexCycle (L6Old r) (L6New r) p
    Sierksma.hexagon_join_cycle.2.1
    (fun i => l6closed_19_hex_fresh _ (by have hh := (Sierksma.l6_orbit_label_geometry.1 r i).2.1; omega))
    (fun i => by have hh := Sierksma.l6_orbit_label_geometry.1 r i; omega)
    (l6closed_19_hex_fresh p hp.1) (L6Replaced r) (Sierksma.l6_replacement_identity r) hfresh
    hg hg' hgb L6Shift Sierksma.l6_orbit_label_geometry.2.2.2.2.1.1 l6closed_19_shift_invariant
    (fun i => (Sierksma.l6_orbit_label_geometry.2.2.2.2.2.1 r i).1)
    (fun i => (Sierksma.l6_orbit_label_geometry.2.2.2.2.2.1 r i).2)
    A (by rw [hA]; norm_num)
    (fun v => (Sierksma.l6_orbit_label_geometry.2.2.2.2.2.2 x y v).trans (hAv _).symm)
  rw [← hcone,PLDegree.signed_count_relabel _ (L6Swap r).injective] at H
  rw [(Sierksma.l6_chain_support_tools.2.1 _ _ _ hold).1,
    (Sierksma.l6_chain_support_tools.2.1 _ _ _ hnew).1] at H
  exact H
end
end

section
open PLDegree Sierksma
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private def l6closed_20_C (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private def l6closed_20_L (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := relabel f
  map_zero' := by simp [relabel]
  map_add' a b := Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
private theorem l6closed_20_inc_list (s : Finset ℕ) :
    listedFace (s.orderEmbOfFin rfl) = Finsupp.single s 1 := by
  unfold listedFace
  have him : Finset.univ.image (s.orderEmbOfFin rfl) = s := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact s.orderEmbOfFin_mem rfl i
    · intro hv
      exact ⟨(s.orderIsoOfFin rfl).symm ⟨v,hv⟩, by simp [Finset.orderEmbOfFin]⟩
  congr 1
  · convert him using 1 <;> ext v <;> simp only [Finset.mem_image]
  · unfold listSign
    have hf : (Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ij h
      exact (not_lt_of_ge ((s.orderEmbOfFin rfl).strictMono (Finset.mem_filter.mp h).2.1).le)
        (Finset.mem_filter.mp h).2.2
    calc
      _ = (-1 : ℤ)^((Finset.univ.filter (fun ij : Fin s.card × Fin s.card =>
        ij.1 < ij.2 ∧ s.orderEmbOfFin rfl ij.2 < s.orderEmbOfFin rfl ij.1)).card) := by
        congr 2
        ext ij
        simp only [Finset.mem_filter]
      _ = 1 := by rw [hf]; simp

private theorem l6closed_20_nat_dEq : ((fun a b => Classical.propDecidable (a=b)) : DecidableEq ℕ)=instDecidableEqNat :=
  Subsingleton.elim _ _
private def l6closed_20_K (y : ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := link y
  map_zero' := by simp [link]
  map_add' a b := Finsupp.sum_add_index'
    (fun _ => by split_ifs <;> simp) (fun _ _ _ => by split_ifs <;> simp [add_smul])
private theorem l6closed_20_incidence_sq (s : Finset ℕ) (y : ℕ) : incidence s y * incidence s y=1 := by
  unfold incidence
  rw [← pow_add,show rank s y+rank s y=2*rank s y by omega,pow_mul]
  simp
private theorem l6closed_20_single_link (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    link y (Finsupp.single s a) =
      if y∈s then a • Finsupp.single (s.erase y) (incidence s y) else 0 := by
  unfold link
  rw [Finsupp.sum_single_index (by split_ifs <;> simp)]
  rw [l6closed_20_nat_dEq]
private theorem l6closed_20_single_cone (s : Finset ℕ) (a : ℤ) (y : ℕ) :
    cone y (Finsupp.single s a)=a • faceCone y s := by
  unfold cone
  rw [Finsupp.sum_single_index (by simp)]
private theorem l6closed_20_fresh_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∉s) :
    Fresh y (Finsupp.single s a) := by
  intro t ht
  have he := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  exact he ▸ hy
private theorem l6closed_20_link_cone (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) :
    l6closed_20_K y (l6closed_20_C y c)=c := by
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hys := hy s hs
  change link y (cone y (Finsupp.single s (c s))) = Finsupp.single s (c s)
  rw [l6closed_20_single_cone]
  unfold faceCone
  rw [l6closed_20_nat_dEq]
  rw [if_neg hys]
  change l6closed_20_K y (c s • Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [map_zsmul]
  change c s • link y (Finsupp.single (insert y s) (incidence (insert y s) y)) = _
  rw [l6closed_20_single_link,if_pos (Finset.mem_insert_self _ _),Finset.erase_insert hys,
    Finsupp.smul_single,smul_eq_mul,l6closed_20_incidence_sq]
  simp
private theorem l6closed_20_cone_link_single (s : Finset ℕ) (a : ℤ) (y : ℕ) (hy : y∈s) :
    cone y (link y (Finsupp.single s a))=Finsupp.single s a := by
  rw [l6closed_20_single_link,if_pos hy]
  change l6closed_20_C y (a • Finsupp.single (s.erase y) (incidence s y)) = _
  rw [map_zsmul]
  change a • cone y (Finsupp.single (s.erase y) (incidence s y)) = _
  rw [l6closed_20_single_cone]
  unfold faceCone
  rw [l6closed_20_nat_dEq]
  rw [if_neg (Finset.notMem_erase y s),Finset.insert_erase hy,
    Finsupp.smul_single,smul_eq_mul,l6closed_20_incidence_sq]
  simp
private theorem l6closed_20_link_fresh (y : ℕ) (c : Chain ℕ) (hy : Fresh y c) : link y c=0 := by
  unfold link
  rw [l6closed_20_nat_dEq]
  apply Finset.sum_eq_zero
  intro s hs
  dsimp only
  rw [if_neg (hy s hs)]
private theorem l6closed_20_relabel_fresh (f : ℕ → ℕ) (hf : Function.Injective f)
    (c : Chain ℕ) (y : ℕ) (hy : Fresh y c) : Fresh (f y) (relabel f c) := by
  intro s hs hyin
  apply Finsupp.mem_support_iff.mp hs
  unfold relabel
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  change (c t • listedFace (f ∘ t.orderEmbOfFin rfl)) s=0
  rw [Finsupp.smul_apply]
  unfold listedFace
  rw [l6closed_20_nat_dEq]
  rw [Finsupp.single_apply]
  split_ifs with he
  · exfalso
    have hfy : f y ∈ Finset.univ.image (f ∘ t.orderEmbOfFin rfl) := he.symm ▸ hyin
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hfy
    exact hy t ht ((hf hi) ▸ t.orderEmbOfFin_mem rfl i)
  · simp

private theorem l6closed_20_link_supported (y : ℕ) (c : Chain ℕ) (t : Finset ℕ)
    (ht : t∈(link y c).support) : ∃ s∈c.support,y∈s ∧ t=s.erase y := by
  by_contra hn
  apply Finsupp.mem_support_iff.mp ht
  unfold link
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro s hs
  dsimp only
  split_ifs with hy
  · rw [Finsupp.smul_apply,Finsupp.single_apply]
    split_ifs with he
    · exfalso
      apply hn
      refine ⟨s,hs,hy,?_⟩
      convert he.symm using 1 <;> ext v <;> simp only [Finset.mem_erase]
    · simp
  · rfl
private theorem l6closed_20_hex_fresh (v : ℕ) (hv : 24≤v) : Fresh v HexCycle := by
  intro t ht hmem
  have hlt := (Sierksma.hexagon_join_cycle.2.2.2 t ht v hmem).1
  omega
theorem Sierksma.l6_bubble_base_tools :
    (∀ r : Fin 8, ∀ i : Fin 3, ∀ s : Finset ℕ,
      s∈(bubble (L6Old r i) (L6New r i) HexCycle).support →
      ∃ t∈HexCycle.support, L6Old r i∈t ∧ s=insert (L6New r i) t) ∧
    (∀ x : EngineParams, EngineGeneric x → ∀ t∈HexCycle.support,
      linearDet (EngineMap x) t≠0)  := by
  constructor
  · intro r i s hs
    obtain ⟨u,hu,hnu,rfl⟩ := Sierksma.l6_chain_support_tools.2.2 _ _ _ hs
    obtain ⟨v,hv,hov,rfl⟩ := Sierksma.l6_chain_support_tools.2.2 _ _ _ hu
    obtain ⟨t,ht,hot,rfl⟩ := l6closed_20_link_supported _ _ _ hv
    exact ⟨t,ht,hot,by rw [Finset.insert_erase hot]⟩
  · intro x hx t ht
    have heq : link 24 (cone 24 HexCycle)=HexCycle :=
      l6closed_20_link_cone 24 HexCycle (l6closed_20_hex_fresh 24 (by norm_num))
    have ht' : t∈(link 24 (cone 24 HexCycle)).support := by rw [heq]; exact ht
    obtain ⟨s,hs,h24,rfl⟩ := l6closed_20_link_supported 24 (cone 24 HexCycle) t ht'
    have H := (hx 0 s hs).2.2 24 h24
    rw [l6closed_20_nat_dEq] at H
    exact H
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
private theorem l6closed_21_row_det_image {m : ℕ} (f : ℕ → ℕ) (hf : Function.Injective f)
    (F : ℕ → Fin m → ℝ) (s : Finset ℕ) (hs : s.card=m)
    (ht : (s.image f).card=m) :
    (Matrix.det (fun i j : Fin m => F ((s.image f).orderEmbOfFin ht i) j) ≠ 0) ↔
      (Matrix.det (fun i j : Fin m => F (f (s.orderEmbOfFin hs i)) j) ≠ 0) := by
  let T := s.image f
  let e : Fin m → Fin m := fun i =>
    (T.orderIsoOfFin ht).symm ⟨f (s.orderEmbOfFin hs i),
      Finset.mem_image_of_mem f (s.orderEmbOfFin_mem hs i)⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg (fun x => ((T.orderIsoOfFin ht x : T) : ℕ)) hij
    have hfv : f (s.orderEmbOfFin hs i)=f (s.orderEmbOfFin hs j) := by simpa [e] using hv
    exact (s.orderEmbOfFin hs).injective (hf hfv)
  let p : Equiv.Perm (Fin m) := Equiv.ofBijective e ⟨he,Finite.surjective_of_injective he⟩
  have hp : ∀ i, T.orderEmbOfFin ht (p i)=f (s.orderEmbOfFin hs i) := by
    intro i
    change (((T.orderIsoOfFin ht) (e i) : T) : ℕ)=_
    simp [e]
  let M : Matrix (Fin m) (Fin m) ℝ := fun i j => F (T.orderEmbOfFin ht i) j
  have hn : (fun i j : Fin m => F (f (s.orderEmbOfFin hs i)) j)=M.submatrix p id := by
    ext i j
    change F (f (s.orderEmbOfFin hs i)) j=F (T.orderEmbOfFin ht (p i)) j
    rw [hp]
  rw [hn,Matrix.det_permute]
  change M.det≠0 ↔ _
  simp
private theorem l6closed_21_aug_image (f : ℕ → ℕ) (hf : Function.Injective f) (F : ℕ → W8)
    (s : Finset ℕ) : augmentedDet F (s.image f)≠0 ↔ augmentedDet (F ∘ f) s≠0 := by
  have hc : (s.image f).card=s.card := Finset.card_image_of_injective s hf
  by_cases hs : s.card=9
  · have ht : (s.image f).card=9 := hc.trans hs
    simp only [augmentedDet,dif_pos hs,dif_pos ht,augmentedMatrix]
    exact l6closed_21_row_det_image f hf (fun v => augment (F v) 1) s hs ht
  · simp [augmentedDet,hs,hc]
private theorem l6closed_21_lin_image (f : ℕ → ℕ) (hf : Function.Injective f) (F : ℕ → W8)
    (s : Finset ℕ) : linearDet F (s.image f)≠0 ↔ linearDet (F ∘ f) s≠0 := by
  have hc : (s.image f).card=s.card := Finset.card_image_of_injective s hf
  by_cases hs : s.card=8
  · have ht : (s.image f).card=8 := hc.trans hs
    simp only [linearDet,dif_pos hs,dif_pos ht]
    exact l6closed_21_row_det_image f hf F s hs ht
  · simp [linearDet,hs,hc]
private theorem l6closed_21_linear_agree (s : Finset ℕ) (F G : ℕ → W8)
    (h : ∀ v ∈ s, F v=G v) : linearDet F s=linearDet G s := by
  unfold linearDet
  split_ifs with hs
  · congr 1
    ext i j
    rw [h _ (s.orderEmbOfFin_mem hs i)]
  · rfl
theorem Sierksma.l6_fresh_point_nonzero (F : ℕ → W8) (t : Finset ℕ)
    (ht : t.card=8) (hlin : linearDet F t≠0) (q : ℕ) (hq : q∉t) :
    (∃ u : W8, augmentedDet (Function.update F q u) (insert q t)≠0) ∧
    (∀ v∈insert q t, ∃ u : W8, linearDet (Function.update F q u) ((insert q t).erase v)≠0)  := by
  have hs : (insert q t).card=9 := by rw [Finset.card_insert_of_notMem hq,ht]
  constructor
  · refine ⟨0,?_⟩
    let S := insert q t
    let i : Fin 9 := (S.orderIsoOfFin hs).symm ⟨q,Finset.mem_insert_self _ _⟩
    have hi : S.orderEmbOfFin hs i=q := by simp [i,Finset.orderEmbOfFin]
    have he : (fun k : Fin 8 => S.orderEmbOfFin hs (i.succAbove k))=t.orderEmbOfFin ht := by
      apply Finset.orderEmbOfFin_unique ht
      · intro k
        have hneq : S.orderEmbOfFin hs (i.succAbove k)≠q := by
          intro h
          have h' := (S.orderEmbOfFin hs).injective (h.trans hi.symm)
          exact Fin.succAbove_ne i k h'
        have hmem := S.orderEmbOfFin_mem hs (i.succAbove k)
        exact (Finset.mem_insert.mp hmem).resolve_left hneq
      · exact (S.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove i)
    let M := augmentedMatrix (Function.update F q 0) S hs
    have hrow : ∀ j : Fin 9, M i j=if j=Fin.last 8 then 1 else 0 := by
      intro j
      change augment (Function.update F q 0 (S.orderEmbOfFin hs i)) 1 j = _
      rw [hi,Function.update_self]
      by_cases hj : j=Fin.last 8
      · subst j
        simp [augment]
      · have hjlt : j.val<8 := by
          have hjn := j.isLt
          have hne : j.val≠8 := fun he => hj (Fin.ext he)
          omega
        simp only [augment,dif_pos hjlt,if_neg hj]
        rfl
    have hminor : M.submatrix i.succAbove (Fin.last 8).succAbove =
        (fun k j : Fin 8 => F (t.orderEmbOfFin ht k) j) := by
      ext k j
      simp only [Matrix.submatrix_apply,Fin.succAbove_last]
      change augment (Function.update F q 0 (S.orderEmbOfFin hs (i.succAbove k))) 1 j.castSucc = _
      rw [congrFun he k]
      rw [Function.update_of_ne (by intro heq; exact hq (heq ▸ t.orderEmbOfFin_mem ht k))]
      simp [augment]
    have hdet : M.det=(-1 : ℝ)^(i.val+8) * linearDet F t := by
      rw [Matrix.det_succ_row M i]
      simp only [hrow]
      rw [Finset.sum_eq_single (Fin.last 8)]
      · rw [if_pos rfl,mul_one,hminor,linearDet,dif_pos ht]
        rfl
      · intro j _ hj
        rw [if_neg hj]
        simp
      · simp
    rw [augmentedDet,dif_pos hs]
    change M.det≠0
    rw [hdet]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hlin
  · intro v hv
    by_cases hvq : v=q
    · subst v
      refine ⟨F q,?_⟩
      rw [Function.update_eq_self,Finset.erase_insert hq]
      exact hlin
    · have hvt : v∈t := (Finset.mem_insert.mp hv).resolve_left hvq
      let σ : Equiv.Perm ℕ := Equiv.swap q v
      have him : t.image σ = (insert q t).erase v := by
        ext w
        simp only [Finset.mem_image,Finset.mem_erase,Finset.mem_insert]
        constructor
        · rintro ⟨a,ha,rfl⟩
          by_cases hav : a=v
          · subst a
            simp [σ,Equiv.swap_apply_right,Ne.symm hvq]
          · have haq : a≠q := fun he => hq (he ▸ ha)
            rw [show σ a=a from Equiv.swap_apply_of_ne_of_ne haq hav]
            exact ⟨hav,Or.inr ha⟩
        · rintro ⟨hwv,hwq|hwt⟩
          · subst w
            exact ⟨v,hvt,by simp [σ]⟩
          · have hwq : w≠q := fun he => hq (he ▸ hwt)
            exact ⟨w,hwt,Equiv.swap_apply_of_ne_of_ne hwq hwv⟩
      refine ⟨F v,?_⟩
      rw [← him]
      apply (l6closed_21_lin_image σ σ.injective (Function.update F q (F v)) t).mpr
      have ha : linearDet ((Function.update F q (F v)) ∘ σ) t=linearDet F t := by
        apply l6closed_21_linear_agree
        intro w hw
        by_cases hwv : w=v
        · subst w
          simp [σ,Function.comp_apply]
        · have hwq : w≠q := fun he => hq (he ▸ hw)
          rw [Function.comp_apply,show σ w=w from Equiv.swap_apply_of_ne_of_ne hwq hwv,
            Function.update_of_ne hwq]
      rw [ha]
      exact hlin
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
set_option maxHeartbeats 800000
private theorem l6closed_22_det_polys
    (F : W8 → ℕ → W8) (E : ℕ → Fin 8 → MvPolynomial (Fin 8) ℝ)
    (hE : ∀ u v j, MvPolynomial.eval u (E v j)=F u v j) :
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 8) ℝ, ∀ u : W8,
      MvPolynomial.eval u p=augmentedDet (F u) s) ∧
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 8) ℝ, ∀ u : W8,
      MvPolynomial.eval u p=linearDet (F u) s) := by
  constructor
  · intro s
    by_cases hs : s.card=9
    · let M : Matrix (Fin 9) (Fin 9) (MvPolynomial (Fin 8) ℝ) := fun i j =>
        if hj : j.val<8 then E (s.orderEmbOfFin hs i) ⟨j.val,hj⟩ else 1
      refine ⟨M.det,?_⟩
      intro u
      rw [RingHom.map_det,augmentedDet,dif_pos hs]
      congr 1
      ext i j
      change MvPolynomial.eval u (M i j)=augment (F u (s.orderEmbOfFin hs i)) 1 j
      dsimp [M,augment]
      split_ifs <;> simp [hE]
    · refine ⟨0,?_⟩
      intro u
      simp [augmentedDet,hs]
  · intro s
    by_cases hs : s.card=8
    · let M : Matrix (Fin 8) (Fin 8) (MvPolynomial (Fin 8) ℝ) := fun i j => E (s.orderEmbOfFin hs i) j
      refine ⟨M.det,?_⟩
      intro u
      rw [RingHom.map_det,linearDet,dif_pos hs]
      congr 1
      ext i j
      exact hE u _ j
    · refine ⟨0,?_⟩
      intro u
      simp [linearDet,hs]
theorem Sierksma.l6_maps_polynomial (x y : EngineParams) (r : Fin 8) :
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 8) ℝ, ∀ u : W8,
      MvPolynomial.eval u p=augmentedDet (EngineMap (L6Aux x r u)) s) ∧
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 8) ℝ, ∀ u : W8,
      MvPolynomial.eval u p=linearDet (EngineMap (L6Aux x r u)) s) ∧
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 8) ℝ, ∀ u : W8,
      MvPolynomial.eval u p=augmentedDet (L6Map y (L6Aux x r u)) s) ∧
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 8) ℝ, ∀ u : W8,
      MvPolynomial.eval u p=linearDet (L6Map y (L6Aux x r u)) s)  := by
  let Y (t : Fin 9) (j : Fin 8) : MvPolynomial (Fin 8) ℝ :=
    if t=r.castSucc then MvPolynomial.X j else MvPolynomial.C (x t j)
  let PR (w : Fin 8 → MvPolynomial (Fin 8) ℝ) : Fin 8 → MvPolynomial (Fin 8) ℝ := fun j =>
    if h : j.val<4 then -w ⟨j.val+4,by omega⟩ else w ⟨j.val-4,by omega⟩-w j
  let E (v : ℕ) : Fin 8 → MvPolynomial (Fin 8) ℝ :=
    if h : v<24 then (PR^[v%6/2]) (Y ⟨2*(v/6)+v%2,by omega⟩)
    else if h' : v<27 then (PR^[v-24]) (Y 8) else 0
  have hY : ∀ u t j,MvPolynomial.eval u (Y t j)=L6Aux x r u t j := by
    intro u t j
    by_cases ht : t=r.castSucc
    · subst t
      simp [Y,L6Aux]
    · simp [Y,L6Aux,ht,Function.update_of_ne ht]
  have hPR : ∀ u w, (fun j => MvPolynomial.eval u (PR w j)) =
      R8 (fun j => MvPolynomial.eval u (w j)) := by
    intro u w
    funext j
    dsimp [PR,R8]
    split_ifs <;> simp
  have hpow : ∀ (k : ℕ) u w,(fun j => MvPolynomial.eval u ((PR^[k]) w j)) =
      (R8^[k]) (fun j => MvPolynomial.eval u (w j)) := by
    intro k
    induction k with
    | zero => intro u w; rfl
    | succ k ih =>
      intro u w
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      exact (hPR u _).trans (congrArg R8 (ih u w))
  have hE : ∀ u v j,MvPolynomial.eval u (E v j)=EngineMap (L6Aux x r u) v j := by
    intro u v j
    unfold EngineMap RPower
    dsimp [E]
    split_ifs
    · have H := congrFun (hpow (v%6/2) u (Y ⟨2*(v/6)+v%2,by omega⟩)) j
      simpa [hY] using H
    · have H := congrFun (hpow (v-24) u (Y 8)) j
      simpa [hY] using H
    · simp
  let D (v : ℕ) (j : Fin 8) : MvPolynomial (Fin 8) ℝ :=
    if v<27 then MvPolynomial.C (EngineMap y v j) else if v<51 then E (v-27) j else 0
  have hD : ∀ u v j,MvPolynomial.eval u (D v j)=L6Map y (L6Aux x r u) v j := by
    intro u v j
    dsimp [D,L6Map]
    split_ifs <;> simp [hE]
  exact ⟨(l6closed_22_det_polys (fun u => EngineMap (L6Aux x r u)) E hE).1,
    (l6closed_22_det_polys (fun u => EngineMap (L6Aux x r u)) E hE).2,
    (l6closed_22_det_polys (fun u => L6Map y (L6Aux x r u)) D hD).1,
    (l6closed_22_det_polys (fun u => L6Map y (L6Aux x r u)) D hD).2⟩
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
set_option maxHeartbeats 800000
theorem Sierksma.l6_finite_gp_avoidance {I : Type*} [Fintype I]
    (F : I → W8 → ℕ → W8) (s : I → Finset ℕ) (hs : ∀ i,(s i).card=9)
    (ha : ∀ i,∃ p : MvPolynomial (Fin 8) ℝ,∀ u : W8,MvPolynomial.eval u p=augmentedDet (F i u) (s i))
    (hl : ∀ i v,∃ p : MvPolynomial (Fin 8) ℝ,∀ u : W8,MvPolynomial.eval u p=linearDet (F i u) ((s i).erase v))
    (hwa : ∀ i,∃ u : W8,augmentedDet (F i u) (s i)≠0)
    (hwl : ∀ i,∀ v∈s i,∃ u : W8,linearDet (F i u) ((s i).erase v)≠0) :
    ∃ u : W8,∀ i,SimplexGP (F i u) (s i)  := by
  classical
  choose pa hpa using ha
  choose pl hpl using hl
  have hpan : ∀ i,pa i≠0 := by
    intro i
    obtain ⟨u,hu⟩ := hwa i
    intro hz
    apply hu
    rw [← hpa i u,hz]
    simp
  have hpln : ∀ i,∀ v∈s i,pl i v≠0 := by
    intro i v hv
    obtain ⟨u,hu⟩ := hwl i v hv
    intro hz
    apply hu
    rw [← hpl i v u,hz]
    simp
  let P : MvPolynomial (Fin 8) ℝ := (∏ i,pa i) * (∏ i,∏ v∈s i,pl i v)
  have hPn : P≠0 := by
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hpan i)
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact Finset.prod_ne_zero_iff.mpr (fun v hv => hpln i v hv)
  obtain ⟨u,hu⟩ := (PLDegree.polynomial_nonzero_open_dense P hPn).2.nonempty
  change MvPolynomial.eval u P≠0 at hu
  dsimp [P] at hu
  rw [map_mul,map_prod,map_prod] at hu
  obtain ⟨hua,hul⟩ := mul_ne_zero_iff.mp hu
  refine ⟨u,?_⟩
  intro i
  refine ⟨hs i,?_,?_⟩
  · rw [← hpa i u]
    exact Finset.prod_ne_zero_iff.mp hua i (Finset.mem_univ _)
  · intro v hv
    have H := Finset.prod_ne_zero_iff.mp hul i (Finset.mem_univ _)
    rw [map_prod] at H
    have H' := Finset.prod_ne_zero_iff.mp H v hv
    rw [hpl i v u] at H'
    convert H' using 1 <;> congr 1 <;> ext w <;> simp only [Finset.mem_erase]
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
set_option maxHeartbeats 800000
private theorem l6closed_24_matrix_agree (s : Finset ℕ) (F G : ℕ → W8)
    (h : ∀ v ∈ s, F v=G v) (hs : s.card=9) :
    augmentedMatrix F s hs=augmentedMatrix G s hs := by
  ext i j
  simp only [augmentedMatrix]
  rw [h _ (s.orderEmbOfFin_mem hs i)]
private theorem l6closed_24_linear_agree (s : Finset ℕ) (F G : ℕ → W8)
    (h : ∀ v ∈ s, F v=G v) : linearDet F s=linearDet G s := by
  unfold linearDet
  split_ifs with hs
  · congr 1
    ext i j
    rw [h _ (s.orderEmbOfFin_mem hs i)]
  · rfl

private theorem l6closed_24_aug_agree (s : Finset ℕ) (F G : ℕ → W8)
    (h : ∀ v∈s,F v=G v) : augmentedDet F s=augmentedDet G s := by
  unfold augmentedDet
  split_ifs with hs
  · rw [l6closed_24_matrix_agree s F G h hs]
  · rfl
private theorem l6closed_24_orbit_value (x : EngineParams) (r : Fin 8) (i : Fin 3) :
    EngineMap x (L6Old r i)=RPower i.val (x r.castSucc) := by
  fin_cases r <;> fin_cases i <;> norm_num [EngineMap,L6Old]
private theorem l6closed_24_power_surjective (i : Fin 3) : Function.Surjective (RPower i.val) := by
  intro w
  fin_cases i
  · exact ⟨w,rfl⟩
  · refine ⟨R8 (R8 w),?_⟩
    exact Sierksma.R8_orientation_preserving.1 w
  · refine ⟨R8 w,?_⟩
    exact Sierksma.R8_orientation_preserving.1 w
theorem Sierksma.l6_bubble_witness_nonzero (x y : EngineParams)
    (hy : EngineGeneric y) (r : Fin 8) (i : Fin 3) (s : Finset ℕ)
    (hs : s∈(bubble (L6Old r i) (L6New r i) HexCycle).support) :
    (s.card=9) ∧
    (∃ u : W8,augmentedDet (L6Map y (L6Aux x r u)) s≠0) ∧
    (∀ v∈s,∃ u : W8,linearDet (L6Map y (L6Aux x r u)) (s.erase v)≠0)  := by
  obtain ⟨t,ht,hot,rfl⟩ := Sierksma.l6_bubble_base_tools.1 r i s hs
  let q := L6New r i
  have hb : ∀ v∈t,v<24 := fun v hv => (Sierksma.hexagon_join_cycle.2.2.2 t ht v hv).1
  have hq : q∉t := by
    intro hqt
    have hh := hb q hqt
    have hn := (Sierksma.l6_orbit_label_geometry.1 r i).2.1
    omega
  have htcard := Sierksma.hexagon_join_cycle.1 t ht
  have hlin := Sierksma.l6_bubble_base_tools.2 y hy t ht
  obtain ⟨haug,hprop⟩ := Sierksma.l6_fresh_point_nonzero (EngineMap y) t htcard hlin q hq
  have hrealize : ∀ w : W8,∃ u : W8,∀ v∈insert q t,
      L6Map y (L6Aux x r u) v=Function.update (EngineMap y) q w v := by
    intro w
    obtain ⟨u,hu⟩ := l6closed_24_power_surjective i w
    refine ⟨u,?_⟩
    intro v hv
    by_cases hvq : v=q
    · subst v
      have hn := (Sierksma.l6_orbit_label_geometry.1 r i).2
      change L6Map y (L6Aux x r u) (L6New r i)=_
      rw [L6Map,if_neg (by omega),if_pos hn.2]
      simp only [L6New,Nat.add_sub_cancel_left]
      rw [l6closed_24_orbit_value,L6Aux,Function.update_self,Function.update_self]
      exact hu
    · have hvt : v∈t := (Finset.mem_insert.mp hv).resolve_left hvq
      rw [L6Map,if_pos (by have hh := hb v hvt; omega),Function.update_of_ne hvq]
  refine ⟨by rw [Finset.card_insert_of_notMem hq,htcard],?_,?_⟩
  · obtain ⟨w,hw⟩ := haug
    obtain ⟨u,hu⟩ := hrealize w
    refine ⟨u,?_⟩
    rw [l6closed_24_aug_agree _ _ _ hu]
    exact hw
  · intro v hv
    obtain ⟨w,hw⟩ := hprop v hv
    obtain ⟨u,hu⟩ := hrealize w
    refine ⟨u,?_⟩
    rw [l6closed_24_linear_agree _ _ _ (fun a ha => hu a (Finset.mem_of_mem_erase ha))]
    exact hw
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
noncomputable section
set_option maxHeartbeats 800000
theorem Sierksma.l6_auxiliary_bubble_gp (x y : EngineParams)
    (hx : EngineGeneric x) (hy : EngineGeneric y) (r : Fin 8)
    (hm : ∀ i : Fin 9, i≠r.castSucc → x i=y i) :
    ∃ u : W8, EngineGeneric (L6Aux x r u) ∧
      (∀ i : Fin 3, ChainGP (L6Map x (L6Aux x r u)) (bubble (L6Old r i) (L6New r i) HexCycle)) ∧
      (∀ i : Fin 3, ChainGP (L6Map y (L6Aux x r u)) (bubble (L6Old r i) (L6New r i) HexCycle))  := by
  classical
  let C := Σ j : Fin 3,(EngineCone j).support
  let B := Σ i : Fin 3,(bubble (L6Old r i) (L6New r i) HexCycle).support
  let I := Sum C (Sum B B)
  let F : I → W8 → ℕ → W8 := Sum.elim (fun _ u => EngineMap (L6Aux x r u))
    (Sum.elim (fun _ u => L6Map x (L6Aux x r u)) (fun _ u => L6Map y (L6Aux x r u)))
  let s : I → Finset ℕ := Sum.elim (fun q => q.2.val)
    (Sum.elim (fun q => q.2.val) (fun q => q.2.val))
  have hcard : ∀ q : I,(s q).card=9 := by
    intro q
    cases q with
    | inl q => exact (hx q.1 q.2.val q.2.property).1
    | inr q =>
      cases q with
      | inl q => exact (Sierksma.l6_bubble_witness_nonzero x x hx r q.1 q.2.val q.2.property).1
      | inr q => exact (Sierksma.l6_bubble_witness_nonzero x y hy r q.1 q.2.val q.2.property).1
  have hpolyA : ∀ q : I,∃ p : MvPolynomial (Fin 8) ℝ,∀ u : W8,
      MvPolynomial.eval u p=augmentedDet (F q u) (s q) := by
    intro q
    cases q with
    | inl q => exact (Sierksma.l6_maps_polynomial x x r).1 q.2.val
    | inr q =>
      cases q with
      | inl q => exact (Sierksma.l6_maps_polynomial x x r).2.2.1 q.2.val
      | inr q => exact (Sierksma.l6_maps_polynomial x y r).2.2.1 q.2.val
  have hpolyL : ∀ q : I,∀ v,∃ p : MvPolynomial (Fin 8) ℝ,∀ u : W8,
      MvPolynomial.eval u p=linearDet (F q u) ((s q).erase v) := by
    intro q v
    cases q with
    | inl q => exact (Sierksma.l6_maps_polynomial x x r).2.1 (q.2.val.erase v)
    | inr q =>
      cases q with
      | inl q => exact (Sierksma.l6_maps_polynomial x x r).2.2.2 (q.2.val.erase v)
      | inr q => exact (Sierksma.l6_maps_polynomial x y r).2.2.2 (q.2.val.erase v)
  have hrest : L6Aux x r (x r.castSucc)=x := by simp [L6Aux]
  have hwa : ∀ q : I,∃ u : W8,augmentedDet (F q u) (s q)≠0 := by
    intro q
    cases q with
    | inl q =>
      refine ⟨x r.castSucc,?_⟩
      change augmentedDet (EngineMap (L6Aux x r (x r.castSucc))) q.2.val≠0
      rw [hrest]
      exact (hx q.1 q.2.val q.2.property).2.1
    | inr q =>
      cases q with
      | inl q => exact (Sierksma.l6_bubble_witness_nonzero x x hx r q.1 q.2.val q.2.property).2.1
      | inr q => exact (Sierksma.l6_bubble_witness_nonzero x y hy r q.1 q.2.val q.2.property).2.1
  have hwl : ∀ q : I,∀ v∈s q,∃ u : W8,linearDet (F q u) ((s q).erase v)≠0 := by
    intro q v hv
    cases q with
    | inl q =>
      refine ⟨x r.castSucc,?_⟩
      change linearDet (EngineMap (L6Aux x r (x r.castSucc))) (q.2.val.erase v)≠0
      rw [hrest]
      convert (hx q.1 q.2.val q.2.property).2.2 v hv using 1 <;>
        congr 1 <;> ext w <;> simp only [Finset.mem_erase]
    | inr q =>
      cases q with
      | inl q =>
        convert (Sierksma.l6_bubble_witness_nonzero x x hx r q.1 q.2.val q.2.property).2.2 v hv using 1 <;>
          congr 1 <;> ext w <;> simp only [Finset.mem_erase]
      | inr q =>
        convert (Sierksma.l6_bubble_witness_nonzero x y hy r q.1 q.2.val q.2.property).2.2 v hv using 1 <;>
          congr 1 <;> ext w <;> simp only [Finset.mem_erase]
  obtain ⟨u,hu⟩ := Sierksma.l6_finite_gp_avoidance F s hcard hpolyA hpolyL hwa hwl
  refine ⟨u,?_,?_,?_⟩
  · intro j t ht
    exact hu (Sum.inl ⟨j,⟨t,ht⟩⟩)
  · intro i t ht
    exact hu (Sum.inr (Sum.inl ⟨i,⟨t,ht⟩⟩))
  · intro i t ht
    exact hu (Sum.inr (Sum.inr ⟨i,⟨t,ht⟩⟩))
end
end

section
open scoped BigOperators
open Common PLDegree Sierksma
set_option maxHeartbeats 800000
theorem proof_Sierksma_pl_orbit_move_multiple_three (x y : EngineParams)
    (hx : EngineGeneric x) (hy : EngineGeneric y) (hm : OneOrbitMove x y) :
    ∀ j : Fin 3, (3 : ℤ) ∣ ConeCount x j-ConeCount y j := by
  obtain ⟨r,hr⟩ := hm
  by_cases h : r=8
  · subst r
    intro j
    rw [Sierksma.l6_apex_move_count x y hx hy hr j,sub_self]
    exact dvd_zero 3
  · let q : Fin 8 := ⟨r.val,by have hh := r.isLt; simp only [Fin.ext_iff] at h; omega⟩
    have hq : q.castSucc=r := Fin.ext rfl
    have hm' : ∀ i : Fin 9,i≠q.castSucc → x i=y i := by simpa [hq] using hr
    obtain ⟨u,hu,hux,huy⟩ := Sierksma.l6_auxiliary_bubble_gp x y hx hy q hm'
    have hxu : ∀ i : Fin 9,i≠q.castSucc → x i=L6Aux x q u i := by
      intro i hi
      simp [L6Aux,Function.update_of_ne hi]
    have hyu : ∀ i : Fin 9,i≠q.castSucc → y i=L6Aux x q u i := by
      intro i hi
      rw [← hm' i hi]
      exact hxu i hi
    have hxmove := Sierksma.l6_generic_orbit_move_count x (L6Aux x q u) hx hu q hxu hux
    have hymove := Sierksma.l6_generic_orbit_move_count y (L6Aux x q u) hy hu q hyu huy
    intro j
    have hdx : (3:ℤ) ∣ ConeCount x j-ConeCount (L6Aux x q u) j := by
      rw [hxmove j]
      exact dvd_mul_right _ _
    have hdy : (3:ℤ) ∣ ConeCount y j-ConeCount (L6Aux x q u) j := by
      rw [hymove j]
      exact dvd_mul_right _ _
    have he : ConeCount x j-ConeCount y j =
        (ConeCount x j-ConeCount (L6Aux x q u) j)-(ConeCount y j-ConeCount (L6Aux x q u) j) := by ring
    rw [he]
    exact dvd_sub hdx hdy
end

