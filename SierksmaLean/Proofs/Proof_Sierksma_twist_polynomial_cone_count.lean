import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
import SierksmaLean.Definitions.Def_Sierksma_Covering
import Mathlib.LinearAlgebra.Matrix.Kronecker
import SierksmaLean.Definitions.Def_PLDegree_BoundaryOperator
import SierksmaLean.Definitions.Def_PLDegree_Chain
section L15Source0
open Common PLDegree Sierksma
open scoped BigOperators

private theorem colorLabel_strictMono (col : Fin 9 → ZMod 3) :
    StrictMono (fun v : Fin 9 => 3*v.val+(col v).val) := by
  intro v w h
  have hv := ZMod.val_lt (col v)
  have hw := ZMod.val_lt (col w)
  have h' : v.val < w.val := h
  dsimp
  omega

private theorem colorFacet_card (col : Fin 9 → ZMod 3) : (ColorFacet col).card=9 := by
  rw [ColorFacet, Finset.card_image_of_injective _ (colorLabel_strictMono col).injective]
  simp

private theorem colorFacet_order (col : Fin 9 → ZMod 3) (i : Fin 9) :
    (ColorFacet col).orderEmbOfFin (colorFacet_card col) i = 3*i.val+(col i).val := by
  have h := Finset.orderEmbOfFin_unique (colorFacet_card col)
    (fun v => Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩) (colorLabel_strictMono col)
  exact congrFun h.symm i

private theorem targetLabel (P : Config 9 3) (v : Fin 9) (j : ZMod 3) :
    TargetTestMap P (3*v.val+j.val)=TestW P v j := by
  have hj := ZMod.val_lt j
  have hlt : 3*v.val+j.val<27 := by omega
  have hdiv : (3*v.val+j.val)/3=v.val := by omega
  have hmod : (3*v.val+j.val)%3=j.val := by omega
  simp [TargetTestMap,hlt,hdiv,hmod]

private theorem colorFacet_matrix (P : Config 9 3) (col : Fin 9 → ZMod 3) :
    augmentedMatrix (TargetTestMap P) (ColorFacet col) (colorFacet_card col) = SignMatrix P col := by
  ext i j
  rw [augmentedMatrix, colorFacet_order, targetLabel]
  by_cases h : j.val<8
  · simp [augment, h, SignMatrix, SignRow, TestW, show j.val≠8 by omega]
  · have hj : j.val=8 := by omega
    simp [augment,h,SignMatrix,SignRow,hj]

theorem Sierksma.L15.color_facet_signed_value (P : Config 9 3) (col : Fin 9 → ZMod 3) :
    (simplexDegree (TargetTestMap P) (ColorFacet col) : ZMod 3) = SignedValue P col := by
  classical
  simp only [simplexDegree, dif_pos (colorFacet_card col), barycentric, colorFacet_matrix]
  simp only [SignedValue, originRow]
  split_ifs <;> simp_all

open Common PLDegree Sierksma
open scoped BigOperators
noncomputable section

private def evalHom (w : Finset ℕ → ℤ) : Chain ℕ →+ ℤ where
  toFun c := evaluate c w
  map_zero' := by simp [evaluate]
  map_add' c d := Finsupp.sum_add_index' (fun s => zero_mul (w s))
    (fun s a b => add_mul a b (w s))

private theorem chi_cast (a : ZMod 3) : (chi a : ZMod 3)=a := by
  have h : ∀ a : ZMod 3, (chi a : ZMod 3)=a := by decide +kernel
  exact h a

theorem Sierksma.L15.color_chain_count (P : Config 9 3) (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) :
    (signedCount (TargetTestMap P) (ColorChain pi c) : ZMod 3) =
      SplitSign pi * ∑ col : Fin 9 → ZMod 3, if col (pi 0)=0 then
        SignedValue P col * ∏ i : Fin 4,
          (col (pi (SplitPosV i))-col (pi (SplitPosU i))-c i) else 0 := by
  classical
  change (((evalHom (simplexDegree (TargetTestMap P))) (ColorChain pi c)) : ZMod 3) = _
  rw [ColorChain, map_sum, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  by_cases hc : col (pi 0)=0
  · simp only [hc, if_true, evalHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      evaluate, Finsupp.sum_single_index, zero_mul, Int.cast_mul, Int.cast_prod,
      chi_cast, Sierksma.L15.color_facet_signed_value, SplitSign]
    ring
  · simp [hc,evalHom,evaluate]
end
end L15Source0

section L15Source1

open scoped BigOperators
open Common Sierksma

private theorem Sierksma.L11.hull_weights (P : Config 9 3) (A : Finset (Fin 9)) (z : Fin 3 → ℝ) :
    z ∈ convexHull ℝ (P '' (A : Set (Fin 9))) ↔
    ∃ w : Fin 9 → ℝ, (∀ v, 0 ≤ w v) ∧ (∀ v, v ∉ A → w v = 0) ∧
      (∑ v, w v) = 1 ∧ (∑ v, w v • P v) = z := by
  classical
  let S : Set (Fin 3 → ℝ) := {z | ∃ w : Fin 9 → ℝ,
    (∀ v, 0 ≤ w v) ∧ (∀ v, v ∉ A → w v = 0) ∧
    (∑ v, w v) = 1 ∧ (∑ v, w v • P v) = z}
  have hS : Convex ℝ S := by
    rintro x ⟨u, hu, hus, hu1, rfl⟩ y ⟨w, hw, hws, hw1, rfl⟩ a b ha hb hab
    refine ⟨fun v => a * u v + b * w v, ?_, ?_, ?_, ?_⟩
    · intro v; exact add_nonneg (mul_nonneg ha (hu v)) (mul_nonneg hb (hw v))
    · intro v hv; simp [hus v hv, hws v hv]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hu1, hw1, hab]
    · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  constructor
  · apply convexHull_min _ hS
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨Pi.single v 1, ?_, ?_, ?_, ?_⟩
    · intro i; by_cases h : i = v <;> simp [h, Pi.single_apply]
    · intro i hi; have h : i ≠ v := by rintro rfl; exact hi hv
      simp [Pi.single_apply, h]
    · simp
    · simp
  · rintro ⟨w, hw, hws, hw1, rfl⟩
    have hs : ∑ v ∈ A, w v = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hws v hv)
    have heq : ∑ v ∈ A, w v • P v = ∑ v, w v • P v :=
      Finset.sum_subset (Finset.subset_univ _) (by intro v _ hv; simp [hws v hv])
    rw [← heq]
    exact (convex_convexHull ℝ _).sum_mem (fun v _ => hw v) hs
      (fun v hv => subset_convexHull ℝ _ ⟨v, hv, rfl⟩)

private theorem Sierksma.L11.zero_iff_common_hull (P : Config 9 3) (A : Finset (Fin 9)) (col : Fin 9 → ZMod 3) :
    ColoredZero P A col ↔ ColoredCommonHull P A col := by
  classical
  have colors : ∀ c : ZMod 3, c=0 ∨ c=1 ∨ c=2 := by decide
  have h01 : (0:ZMod 3) ≠ 1 := by decide
  have h02 : (0:ZMod 3) ≠ 2 := by decide
  have h12 : (1:ZMod 3) ≠ 2 := by decide
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h21 := Ne.symm h12
  let X (w : Fin 9 → ℝ) (j : ZMod 3) (k : Fin 4) :=
    ∑ v, if col v = j then w v * LiftCoord P v k.val else 0
  have row0 (v : Fin 9) (k : Fin 4) :
      TestW P v (col v) ⟨k.val, by omega⟩ =
        (if col v = 1 then LiftCoord P v k.val else 0) -
        (if col v = 0 then LiftCoord P v k.val else 0) := by
    rcases colors (col v) with hc | hc | hc <;> simp [TestW, k.isLt, hc, h01, h02, h12, h10, h20, h21]
  have row1 (v : Fin 9) (k : Fin 4) :
      TestW P v (col v) ⟨k.val + 4, by omega⟩ =
        (if col v = 2 then LiftCoord P v k.val else 0) -
        (if col v = 0 then LiftCoord P v k.val else 0) := by
    rcases colors (col v) with hc | hc | hc <;> simp [TestW, show ¬ k.val + 4 < 4 by omega, hc, h01, h02, h12, h10, h20, h21]
  have balance (w : Fin 9 → ℝ) :
      (∑ v, w v • TestW P v (col v)) = 0 ↔
        ∀ k : Fin 4, X w 1 k = X w 0 k ∧ X w 2 k = X w 0 k := by
    have eq0 (k : Fin 4) :
        (∑ v, w v • TestW P v (col v)) ⟨k.val, by omega⟩ = X w 1 k - X w 0 k := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row0, mul_sub,
        mul_ite, mul_zero, Finset.sum_sub_distrib, X]
    have eq1 (k : Fin 4) :
        (∑ v, w v • TestW P v (col v)) ⟨k.val + 4, by omega⟩ = X w 2 k - X w 0 k := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row1, mul_sub,
        mul_ite, mul_zero, Finset.sum_sub_distrib, X]
    constructor
    · intro h k
      have h0 := congrFun h (⟨k.val, by omega⟩ : Fin 8)
      have h1 := congrFun h (⟨k.val + 4, by omega⟩ : Fin 8)
      rw [eq0] at h0; rw [eq1] at h1
      exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
    · intro h; funext k
      by_cases hk : k.val < 4
      · have he : k = (⟨k.val, by omega⟩ : Fin 8) := rfl
        rw [he, eq0 ⟨k.val,hk⟩, (h ⟨k.val, hk⟩).1, sub_self]; rfl
      · have he : k = (⟨(k.val-4)+4, by omega⟩ : Fin 8) := by apply Fin.ext; dsimp; omega
        rw [he, eq1 ⟨k.val-4, by omega⟩, (h ⟨k.val-4, by omega⟩).2, sub_self]; rfl
  constructor
  · rintro ⟨w, hw, hws, hw1, hw0⟩
    have hb := (balance w).mp hw0
    have htotal : X w 0 3 + X w 1 3 + X w 2 3 = 1 := by
      rw [← hw1]
      simp only [X, LiftCoord, show ¬ (3:ℕ) < 3 by omega, dif_neg, mul_one]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _; rcases colors (col v) with hc | hc | hc <;> simp [hc, h01, h02, h12, h10, h20, h21]
    have hm (j : ZMod 3) : X w j 3 = 1/3 := by
      have h := hb 3
      rcases colors j with rfl | rfl | rfl <;> linarith [h.1, h.2]
    let u (j : ZMod 3) (v : Fin 9) := if col v = j then 3*w v else 0
    have hu (j : ZMod 3) :
        (∀ v, 0 ≤ u j v) ∧ (∀ v, v ∉ ColorBlock A col j → u j v=0) ∧
        (∑ v, u j v)=1 ∧ (∑ v, u j v • P v) = (fun k : Fin 3 => 3*X w 0 k.castSucc) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v; dsimp [u]; split_ifs
        · exact mul_nonneg (by norm_num) (hw v)
        · exact le_rfl
      · intro v hv
        by_cases hc : col v = j
        · have hA : v ∉ A := by simpa [ColorBlock, hc] using hv
          simp [u, hc, hws v hA]
        · simp [u, hc]
      · have he : (∑ v, u j v) = 3*X w j 3 := by
          simp [u, X, LiftCoord, Finset.mul_sum, mul_ite]
        rw [he, hm]; norm_num
      · funext k
        have he : (∑ v, u j v • P v) k = 3*X w j k.castSucc := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u, X,
            LiftCoord, Fin.val_castSucc, k.isLt, dif_pos, ite_mul, zero_mul]
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl
          intro v _; split_ifs <;> ring
        rw [he]
        rcases colors j with rfl | rfl | rfl
        · rfl
        · rw [(hb k.castSucc).1]
        · rw [(hb k.castSucc).2]
    refine ⟨?_, ⟨fun k => 3*X w 0 k.castSucc, ?_⟩⟩
    · intro j
      by_contra hn
      have hempty : ColorBlock A col j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hz : ∀ v, u j v=0 := fun v => (hu j).2.1 v (by simp [hempty])
      have := (hu j).2.2.1
      simp [hz] at this
    · intro j; exact (Sierksma.L11.hull_weights P _ _).mpr ⟨u j, hu j⟩
  · rintro ⟨hne, z, hz⟩
    have hc : ∀ j : ZMod 3, ∃ u : Fin 9 → ℝ, (∀ v, 0 ≤ u v) ∧
        (∀ v, v ∉ ColorBlock A col j → u v=0) ∧ (∑ v, u v)=1 ∧ (∑ v, u v • P v)=z :=
      fun j => (Sierksma.L11.hull_weights P _ z).mp (hz j)
    choose u hu hus hu1 huz using hc
    have huoff (j : ZMod 3) (v : Fin 9) (h : col v ≠ j) : u j v=0 :=
      hus j v (by simp [ColorBlock, h])
    let w (v : Fin 9) := (u 0 v + u 1 v + u 2 v)/3
    have hx (j : ZMod 3) (k : Fin 4) :
        X w j k = (∑ v, u j v * LiftCoord P v k.val)/3 := by
      change (∑ v, if col v = j then w v * LiftCoord P v k.val else 0) = _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      dsimp [X, w]
      rcases colors j with rfl | rfl | rfl <;>
        rcases colors (col v) with hc | hc | hc <;>
        have off0 : col v ≠ 0 → u 0 v = 0 := huoff 0 v <;>
        have off1 : col v ≠ 1 → u 1 v = 0 := huoff 1 v <;>
        have off2 : col v ≠ 2 → u 2 v = 0 := huoff 2 v <;>
        simp [hc, h01, h02, h12, h10, h20, h21] at off0 off1 off2 ⊢ <;>
        simp_all only [add_zero, zero_add, zero_mul] <;> ring
    refine ⟨w, ?_, ?_, ?_, (balance w).mpr ?_⟩
    · intro v; dsimp [w]; exact div_nonneg (add_nonneg (add_nonneg (hu 0 v) (hu 1 v)) (hu 2 v)) (by norm_num)
    · intro v hv; simp [w, hus 0 v (by simp [ColorBlock, hv]),
        hus 1 v (by simp [ColorBlock, hv]), hus 2 v (by simp [ColorBlock, hv])]
    · dsimp [w]; rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hu1, hu1, hu1]; norm_num
    · intro k
      have he (j : ZMod 3) : (∑ v, u j v * LiftCoord P v k.val) =
          if h : k.val<3 then z ⟨k.val,h⟩ else 1 := by
        by_cases h : k.val<3
        · simpa [LiftCoord, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
            congrFun (huz j) ⟨k.val,h⟩
        · simp [LiftCoord, h, hu1]
      constructor <;> rw [hx, hx, he, he]

open Common Sierksma
set_option autoImplicit false

private theorem l18aRankInjective {n : ℕ}
    (s : Finset (Fin n)) (hs : s.card = 3) (x y : Fin n)
    (hx : x ∈ s) (hy : y ∈ s) :
    ((s.filter (fun z => z < x)).card : ZMod 3) =
      ((s.filter (fun z => z < y)).card : ZMod 3) ↔ x = y := by
  classical
  have rank_lt (a : Fin n) (ha : a ∈ s) :
      (s.filter (fun z => z < a)).card < 3 := by
    rw [← hs]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have ham : a ∈ s.filter (fun z => z < a) := he.symm ▸ ha
    exact (lt_irrefl a) (Finset.mem_filter.mp ham).2
  have rank_strict (a b : Fin n) (ha : a ∈ s) (hab : a < b) :
      (s.filter (fun z => z < a)).card <
        (s.filter (fun z => z < b)).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hz).1, lt_trans (Finset.mem_filter.mp hz).2 hab⟩
    · intro he
      have ham : a ∈ s.filter (fun z => z < a) :=
        he.symm ▸ Finset.mem_filter.mpr ⟨ha, hab⟩
      exact (lt_irrefl a) (Finset.mem_filter.mp ham).2
  constructor
  · intro h
    have hr : (s.filter (fun z => z < x)).card =
        (s.filter (fun z => z < y)).card := by
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast_of_lt (rank_lt x hx),
        ZMod.val_natCast_of_lt (rank_lt y hy)] using hv
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · exact False.elim ((ne_of_lt (rank_strict x y hx hxy)) hr)
    · exact hxy
    · exact False.elim ((ne_of_lt (rank_strict y x hy hyx)) hr.symm)
  · intro h
    subst y
    rfl

private theorem Sierksma.canon_colour_respects {n : ℕ}
    (Q : Common.Partition n) (hQ : IsPartition Q 3) :
    Respects Q (CanonColour Q) := by
  classical
  obtain ⟨⟨hne, hdisj, hcover⟩, hcard⟩ := hQ
  have unique (A B : Block n) (hA : A ∈ Q) (hB : B ∈ Q)
      (v : Fin n) (hvA : v ∈ A) (hvB : v ∈ B) : A = B := by
    by_contra hab
    exact (Finset.disjoint_left.mp (hdisj A hA B hB hab)) hvA hvB
  have block_exists (v : Fin n) : ∃ A ∈ Q, v ∈ A := by
    have hv : v ∈ Q.biUnion id := hcover.symm ▸ Finset.mem_univ v
    simpa only [Finset.mem_biUnion, id_eq] using hv
  let m : {A : Block n // A ∈ Q} → Fin n :=
    fun A => A.val.min' (hne A.val A.property).1
  have m_mem (A : {A : Block n // A ∈ Q}) : m A ∈ A.val :=
    Finset.min'_mem _ _
  have m_le (A : {A : Block n // A ∈ Q}) (v : Fin n) (hv : v ∈ A.val) :
      m A ≤ v := Finset.min'_le _ v hv
  have m_inj : Function.Injective m := by
    intro A B h
    apply Subtype.ext
    apply unique A.val B.val A.property B.property (m A) (m_mem A)
    rw [h]
    exact m_mem B
  let M : Finset (Fin n) := Finset.univ.image m
  have M_card : M.card = 3 := by
    dsimp [M]
    rw [Finset.card_image_of_injective _ m_inj]
    simpa only [Finset.card_univ, Fintype.card_coe, Finset.card_attach] using hcard
  have m_in_M (A : {A : Block n // A ∈ Q}) : m A ∈ M := by
    exact Finset.mem_image.mpr ⟨A, Finset.mem_univ A, rfl⟩
  have minimum_iff (u : Fin n) :
      (∀ w : Fin n, w < u → ¬ ∃ A ∈ Q, w ∈ A ∧ u ∈ A) ↔ u ∈ M := by
    constructor
    · intro hu
      obtain ⟨A, hA, huA⟩ := block_exists u
      let a : {A : Block n // A ∈ Q} := ⟨A, hA⟩
      have hmu : m a = u := by
        apply le_antisymm (m_le a u huA)
        apply le_of_not_gt
        intro hlt
        exact hu (m a) hlt ⟨A, hA, m_mem a, huA⟩
      rw [← hmu]
      exact m_in_M a
    · intro hu w hwu ⟨B, hB, hwB, huB⟩
      obtain ⟨a, _, hma⟩ := Finset.mem_image.mp hu
      have hab : a.val = B :=
        unique a.val B a.property hB u (hma ▸ m_mem a) huB
      have hwA : w ∈ a.val := hab.symm ▸ hwB
      have hle : u ≤ w := hma ▸ m_le a w hwA
      exact (not_lt_of_ge hle) hwu
  have below_iff (v : Fin n) (a : {A : Block n // A ∈ Q}) (hv : v ∈ a.val)
      (u : Fin n) :
      (∀ w : Fin n, (∃ A ∈ Q, w ∈ A ∧ v ∈ A) → u < w) ↔ u < m a := by
    constructor
    · intro h
      exact h (m a) ⟨a.val, a.property, m_mem a, hv⟩
    · intro h w ⟨B, hB, hwB, hvB⟩
      have hab : a.val = B := unique a.val B a.property hB v hv hvB
      exact lt_of_lt_of_le h (m_le a w (hab.symm ▸ hwB))
  have colour_eq (v : Fin n) (a : {A : Block n // A ∈ Q}) (hv : v ∈ a.val) :
      CanonColour Q v = ((M.filter (fun u => u < m a)).card : ZMod 3) := by
    unfold CanonColour
    apply congrArg (fun s : Finset (Fin n) => (s.card : ZMod 3))
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      minimum_iff u, below_iff v a hv u]
  intro u v
  obtain ⟨A, hA, huA⟩ := block_exists u
  obtain ⟨B, hB, hvB⟩ := block_exists v
  let a : {A : Block n // A ∈ Q} := ⟨A, hA⟩
  let b : {A : Block n // A ∈ Q} := ⟨B, hB⟩
  rw [colour_eq u a huA, colour_eq v b hvB]
  constructor
  · intro h
    have hm : m a = m b :=
      (l18aRankInjective M M_card (m a) (m b)
        (m_in_M a) (m_in_M b)).mp h
    have hab : a = b := m_inj hm
    have hAB : A = B := congrArg Subtype.val hab
    exact ⟨A, hA, huA, hAB.symm ▸ hvB⟩
  · rintro ⟨C, hC, huC, hvC⟩
    have hAC : A = C := unique A C hA hC u huA huC
    have hBC : B = C := unique B C hB hC v hvB hvC
    have hab : a = b := Subtype.ext (hAC.trans hBC.symm)
    rw [hab]

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
private theorem Sierksma.respects_two_orientations {n : ℕ} (Q : Common.Partition n) (c d : Fin n → ZMod 3) (hc : Sierksma.Respects Q c) (hd : Sierksma.Respects Q d) (u v : Fin n) (hne : c u ≠ c v) : (∀ x y, d y - d x = c y - c x) ∨ (∀ x y, d y - d x = -(c y - c x)) := by
  have scalar : ∀ a b c d x y : ZMod 3, a ≠ b → c ≠ d → (x = a ↔ y = c) → (x = b ↔ y = d) → (d-c)*(x-a) = (b-a)*(y-c) := by decide
  have kernel : ∀ x y, c x = c y ↔ d x = d y := fun x y => (hc x y).trans (hd x y).symm
  have hdne : d u ≠ d v := fun h => hne ((kernel u v).mpr h)
  let a : ZMod 3 := (d v - d u) / (c v - c u)
  have hcu : c v - c u ≠ 0 := sub_ne_zero.mpr hne.symm
  have hdu : d v - d u ≠ 0 := sub_ne_zero.mpr hdne.symm
  have ha : a ≠ 0 := div_ne_zero hdu hcu
  have hx : ∀ x, d x - d u = a * (c x - c u) := by
    intro x
    have h := scalar (c u) (c v) (d u) (d v) (c x) (d x) hne hdne (kernel x u) (kernel x v)
    dsimp [a]
    field_simp
    linear_combination -h
  have hs : a = 1 ∨ a = -1 := by
    revert ha
    generalize a = z
    decide +revert
  rcases hs with hs | hs
  · left
    intro x y
    have h1 := hx x
    have h2 := hx y
    rw [hs, one_mul] at h1 h2
    linear_combination h2-h1
  · right
    intro x y
    have h1 := hx x
    have h2 := hx y
    rw [hs, neg_one_mul] at h1 h2
    linear_combination h2-h1

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open scoped BigOperators Kronecker
open Common Sierksma

private theorem colour_even_products_local (col : Fin 9 → ZMod 3) (pi : Equiv.Perm (ZMod 3)) :
    (∀ e e' : Edge 9,
      (pi (col e.2)-pi (col e.1))*(pi (col e'.2)-pi (col e'.1))=
        (col e.2-col e.1)*(col e'.2-col e'.1)) ∧
    (∀ es : Fin 4 → Edge 9,
      (∏ i, (pi (col (es i).2)-pi (col (es i).1)))=
        ∏ i, (col (es i).2-col (es i).1)) := by
  have hf : ∀ f : ZMod 3 → ZMod 3, Function.Injective f →
      (f 1-f 0)^2=1 ∧ ∀ j, f j=(f 1-f 0)*j+f 0 := by
    decide +kernel
  obtain ⟨ha, hform⟩ := hf pi pi.injective
  let a : ZMod 3 := pi 1-pi 0
  have hd (u v : ZMod 3) : pi v-pi u=a*(v-u) := by
    rw [hform v, hform u]
    dsimp [a]
    ring
  constructor
  · intro e e'
    rw [hd, hd]
    calc
      a*(col e.2-col e.1)*(a*(col e'.2-col e'.1)) =
          a^2*((col e.2-col e.1)*(col e'.2-col e'.1)) := by ring
      _ = _ := by rw [show a^2=1 from ha, one_mul]
  · intro es
    simp_rw [hd]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    norm_num
    have hfour : a^4=1 := by calc
      a^4=(a^2)^2 := by ring
      _=1 := by rw [show a^2=1 from ha]; norm_num
    rw [hfour, one_mul]

private theorem colour_matrix_transport_local (P : Config 9 3) (col : Fin 9 → ZMod 3) (pi : Equiv.Perm (ZMod 3)) :
    ∃ U : Matrix (Fin 9) (Fin 9) ℝ, U.det = 1 ∧
      SignMatrix P (pi ∘ col) = SignMatrix P col * U ∧
      Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) U = Pi.single (8 : Fin 9) (1 : ℝ) := by
  let q : ZMod 3 → Fin 2 → ℤ := fun k => if k=0 then ![-1,-1] else if k=1 then ![1,0] else ![0,1]
  let t : ZMod 3 → Fin 2 → ℝ := fun k i => (q k i : ℝ)
  let B : Matrix (Fin 2) (Fin 2) ℝ := fun i j => t (pi (if i=0 then 1 else 2)) j
  let e : ((Fin 2 × Fin 4) ⊕ Fin 1) ≃ Fin 9 :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  let D : Matrix ((Fin 2 × Fin 4) ⊕ Fin 1) ((Fin 2 × Fin 4) ⊕ Fin 1) ℝ :=
    Matrix.fromBlocks (B ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) 0 0 1
  let U := Matrix.reindex e e D
  have hB : B.det^4=1 := by
    have hq : ∀ a b : ZMod 3, a≠b →
        (q a 0*q b 1-q a 1*q b 0)^4=1 := by decide +kernel
    have hz := hq (pi 1) (pi 2) (pi.injective.ne (by decide))
    rw [Matrix.det_fin_two]
    change ((q (pi 1) 0 : ℝ)*(q (pi 2) 1 : ℝ)-(q (pi 1) 1 : ℝ)*(q (pi 2) 0 : ℝ))^4=1
    exact_mod_cast hz
  have hU : U.det=1 := by
    change (Matrix.reindex e e D).det=1
    rw [Matrix.det_reindex_self]
    dsimp only [D]
    rw [ Matrix.det_fromBlocks_zero₂₁, Matrix.det_kronecker]
    simpa using hB
  have hform : ∀ k : ZMod 3, ∀ j : Fin 2,
      t (pi k) j = ∑ i : Fin 2, t k i * B i j := by
    have hq : ∀ f : ZMod 3 → ZMod 3, Function.Injective f → ∀ k : ZMod 3, ∀ j : Fin 2,
        q (f k) j = ∑ i : Fin 2, q k i * q (f (if i=0 then 1 else 2)) j := by decide +kernel
    intro k j
    have hz := hq pi pi.injective k j
    dsimp only [B,t]
    exact_mod_cast hz
  have hentry (i j : Fin 9) : U i j =
      if h : i.val<8 ∧ j.val<8 ∧ i.val%4=j.val%4 then
        B ⟨i.val/4, by omega⟩ ⟨j.val/4, by omega⟩
      else if i=8 ∧ j=8 then 1 else 0 := by
    fin_cases i <;> fin_cases j <;>
      simp +decide [U,D,e,Matrix.reindex_apply,Matrix.fromBlocks,Matrix.kroneckerMap,Matrix.one_apply,finProdFinEquiv,finSumFinEquiv,Fin.addCases,Fin.divNat,Fin.modNat]
  have hrow (cl : Fin 9 → ZMod 3) (v : Fin 9) (b : Fin 2) (l : Fin 4) :
      SignMatrix P cl v ⟨4*b.val+l.val, by omega⟩ = LiftCoord P v l.val * t (cl v) b := by
    fin_cases b <;> fin_cases l
    all_goals
      by_cases h0 : cl v=0 <;> by_cases h1 : cl v=1 <;>
        simp [SignMatrix,SignRow,t,q,h0,h1]
  have hrow2 (cl : Fin 9 → ZMod 3) (v j : Fin 9) (hj : j.val<8) :
      SignMatrix P cl v j = LiftCoord P v (j.val%4) * t (cl v) ⟨j.val/4,by omega⟩ := by
    have he : (⟨4*(j.val/4)+j.val%4, by omega⟩ : Fin 9)=j := by
      apply Fin.ext
      change 4*(j.val/4)+j.val%4=j.val
      omega
    simpa only [he] using hrow cl v ⟨j.val/4,by omega⟩ ⟨j.val%4,Nat.mod_lt _ (by omega)⟩
  refine ⟨U,hU,?_,?_⟩
  · ext v j
    fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 0 (by decide),hrow2 col v 0 (by decide),hrow2 col v 4 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 1 (by decide),hrow2 col v 1 (by decide),hrow2 col v 5 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 2 (by decide),hrow2 col v 2 (by decide),hrow2 col v 6 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 3 (by decide),hrow2 col v 3 (by decide),hrow2 col v 7 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 4 (by decide),hrow2 col v 0 (by decide),hrow2 col v 4 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 5 (by decide),hrow2 col v 1 (by decide),hrow2 col v 5 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 6 (by decide),hrow2 col v 2 (by decide),hrow2 col v 6 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_succ]
      simp +decide [hentry]
      rw [hrow2 (pi ∘ col) v 7 (by decide),hrow2 col v 3 (by decide),hrow2 col v 7 (by decide)]
      simp only [Function.comp_apply]
      rw [hform]
      norm_num [Fin.sum_univ_two,Fin.coe_ofNat_eq_mod]
      ring
    · simp [Matrix.mul_apply,Fin.sum_univ_succ,hentry,SignMatrix,SignRow]
  · rw [Matrix.single_vecMul, one_smul]
    ext j
    fin_cases j <;> rfl

theorem Sierksma.signed_determinant_colour_invariant (P : Config 9 3) (col : Fin 9 → ZMod 3) (pi : Equiv.Perm (ZMod 3)) :
    (SignMatrix P (pi ∘ col)).det=(SignMatrix P col).det ∧
    SignedValue P (pi ∘ col)=SignedValue P col ∧
    (∀ e e' : Edge 9,
      (pi (col e.2)-pi (col e.1))*(pi (col e'.2)-pi (col e'.1))=
        (col e.2-col e.1)*(col e'.2-col e'.1)) ∧
    (∀ es : Fin 4 → Edge 9,
      (∏ i, (pi (col (es i).2)-pi (col (es i).1)))=
        ∏ i, (col (es i).2-col (es i).1)) := by
  obtain ⟨U,hU,hm,ht⟩ := colour_matrix_transport_local P col pi
  have hd : (SignMatrix P (pi ∘ col)).det=(SignMatrix P col).det := by
    rw [hm,Matrix.det_mul,hU,mul_one]
  have htinv : Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) U⁻¹ =
      Pi.single (8 : Fin 9) (1 : ℝ) := by
    calc
      _ = Matrix.vecMul (Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) U) U⁻¹ := by rw [ht]
      _ = Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) (U*U⁻¹) := Matrix.vecMul_vecMul _ _ _
      _ = _ := by rw [Matrix.mul_nonsing_inv U (by simp [hU]),Matrix.vecMul_one]
  have hvec : Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) (SignMatrix P (pi ∘ col))⁻¹ =
      Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) (SignMatrix P col)⁻¹ := by
    rw [hm,Matrix.mul_inv_rev,← Matrix.vecMul_vecMul,htinv]
  exact ⟨hd,by simp only [SignedValue,hd,hvec],colour_even_products_local col pi⟩

open Common PLDegree Sierksma
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

private theorem signedValue_surj (P : Config 9 3) (col : Fin 9 → ZMod 3)
    (hs : SignedValue P col ≠ 0) : Function.Surjective col := by
  classical
  let M := SignMatrix P col
  let b : Fin 9 → ℝ := Pi.single 8 1
  let lam := Matrix.vecMul b M⁻¹
  have hc : M.det ≠ 0 ∧ ∀ v, 0 < lam v := by
    by_contra hn
    have hn' : ¬((SignMatrix P col).det ≠ 0 ∧
      ∀ v, 0 < Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) (SignMatrix P col)⁻¹ v) := hn
    exact hs (by rw [SignedValue,if_neg hn'])
  have he : Matrix.vecMul lam M=b := by
    dsimp [lam]
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hc.1),Matrix.vecMul_one]
  have h1 : ∑ v, lam v=1 := by
    have h := congrFun he 8
    simpa [Matrix.vecMul,dotProduct,M,SignMatrix,SignRow,b] using h
  have h0 : ∑ v, lam v • TestW P v (col v)=0 := by
    funext k
    have h := congrFun he k.castSucc
    have hk : k.castSucc ≠ (8 : Fin 9) := by
      intro hh; have hh' := congrArg Fin.val hh; dsimp at hh'; omega
    simpa [Matrix.vecMul,dotProduct,M,SignMatrix,SignRow,TestW,
      show k.val≠8 by omega,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,b,Pi.single_apply,hk] using h
  have hz : ColoredZero P Finset.univ col :=
    ⟨lam,fun v => (hc.2 v).le,by simp,h1,h0⟩
  have hh := (Sierksma.L11.zero_iff_common_hull P _ col).mp hz
  intro j
  obtain ⟨v,hv⟩ := hh.1 j
  exact ⟨v,(Finset.mem_filter.mp hv).2⟩

private theorem coloredBlocks_partition (col : Fin 9 → ZMod 3)
    (hs : Function.Surjective col) : IsPartition (ColoredBlocks Finset.univ col) 3 := by
  classical
  let B := ColorBlock (Finset.univ : Finset (Fin 9)) col
  have hne (j : ZMod 3) : (B j).Nonempty := by
    obtain ⟨v,hv⟩ := hs j
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩
  have hi : Function.Injective B := by
    intro j k h
    obtain ⟨v,hv⟩ := hne j
    have hvk : v ∈ B k := h ▸ hv
    exact (Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hvk).2
  have hQ : ColoredBlocks Finset.univ col = Finset.univ.image B := by
    apply Finset.filter_eq_self.mpr
    intro A hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hA
    exact hne j
  rw [hQ]
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro A hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨hne j,Finset.subset_univ _⟩
  · intro A hA C hC hac
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hC
    apply Finset.disjoint_left.mpr
    intro v hv hw
    apply hac
    congr 1
    exact (Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hw).2
  · ext v
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · intro _; trivial
    · intro _
      exact ⟨B (col v),⟨col v,rfl⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  · rw [Finset.card_image_of_injective _ hi]
    simp

private theorem coloredBlocks_respects (col : Fin 9 → ZMod 3) :
    Respects (ColoredBlocks Finset.univ col) col := by
  classical
  intro u v
  constructor
  · intro h
    refine ⟨ColorBlock Finset.univ col (col u),?_,?_,?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨col u,Finset.mem_univ _,rfl⟩,
        ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩⟩
    · simp [ColorBlock]
    · simp [ColorBlock,h]
  · rintro ⟨A,hA,hu,hv⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hA).1
    exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm

private theorem respects_fibres (Q : Common.Partition 9) (hQ : IsPartition Q 3)
    (col : Fin 9 → ZMod 3) (hr : Respects Q col) :
    Function.Surjective col ∧ ColoredBlocks Finset.univ col=Q := by
  classical
  have hne : ∀ A : Q, A.val.Nonempty := fun A => (hQ.1.1 A.val A.property).1
  choose v hv using hne
  have hf (A : Q) : ColorBlock Finset.univ col (col (v A))=A.val := by
    ext u
    simp only [ColorBlock,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hc
      obtain ⟨B,hB,hu,hvB⟩ := (hr u (v A)).mp hc
      by_cases he : B=A.val
      · simpa [he] using hu
      · exact False.elim ((Finset.disjoint_left.mp (hQ.1.2.1 B hB A.val A.property he)) hvB (hv A))
    · intro hu
      exact (hr u (v A)).mpr ⟨A.val,A.property,hu,hv A⟩
  have hi : Function.Injective (fun A : Q => col (v A)) := by
    intro A B he
    change col (v A)=col (v B) at he
    apply Subtype.ext
    rw [←hf A,←hf B,he]
  have hcard : Fintype.card Q = Fintype.card (ZMod 3) := by simpa using hQ.2
  have hsur := ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,hcard⟩).2
  refine ⟨fun j => ?_,?_⟩
  · obtain ⟨A,hA⟩ := hsur j
    exact ⟨v A,hA⟩
  · ext A
    constructor
    · intro hA
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hA).1
      obtain ⟨B,hB⟩ := hsur j
      rw [←hB,hf]
      exact B.property
    · intro hA
      refine Finset.mem_filter.mpr ⟨?_,(hQ.1.1 A hA).1⟩
      exact Finset.mem_image.mpr ⟨col (v ⟨A,hA⟩),Finset.mem_univ _,hf ⟨A,hA⟩⟩

private def normCol (s : Fin 9) (Q : Common.Partition 9) (b : Bool) (v : Fin 9) : ZMod 3 :=
  if b then CanonColour Q v-CanonColour Q s else -(CanonColour Q v-CanonColour Q s)

private theorem normCol_respects (s : Fin 9) (Q : Common.Partition 9)
    (hQ : IsPartition Q 3) (b : Bool) : Respects Q (normCol s Q b) := by
  have hr := Sierksma.canon_colour_respects Q hQ
  intro u v
  cases b <;> simpa [normCol] using hr u v

private theorem normCol_surj (s : Fin 9) (Q : Common.Partition 9)
    (hQ : IsPartition Q 3) (b : Bool) : Function.Surjective (normCol s Q b) :=
  (respects_fibres Q hQ _ (normCol_respects s Q hQ b)).1

private theorem normCol_base (s : Fin 9) (Q : Common.Partition 9) (b : Bool) :
    normCol s Q b s=0 := by cases b <;> simp [normCol]

private theorem normCol_ne (s : Fin 9) (Q : Common.Partition 9) (hQ : IsPartition Q 3) :
    normCol s Q true ≠ normCol s Q false := by
  obtain ⟨v,hv⟩ := normCol_surj s Q hQ true 1
  intro h
  have hh := congrFun h v
  have hneg : normCol s Q false v= - normCol s Q true v := by simp [normCol]
  rw [hneg,hv] at hh
  have h1 : (1:ZMod 3) ≠ -1 := by decide +kernel
  exact h1 hh

private theorem normalized_form (s : Fin 9) (Q : Common.Partition 9) (hQ : IsPartition Q 3)
    (col : Fin 9 → ZMod 3) (hr : Respects Q col) (hn : col s=0) :
    col=normCol s Q true ∨ col=normCol s Q false := by
  have hc := Sierksma.canon_colour_respects Q hQ
  have hs := (respects_fibres Q hQ _ hc).1
  obtain ⟨u,hu⟩ := hs 0
  obtain ⟨v,hv⟩ := hs 1
  have hne : CanonColour Q u ≠ CanonColour Q v := by rw [hu,hv]; decide +kernel
  rcases Sierksma.respects_two_orientations Q (CanonColour Q) col hc hr u v hne with hp | hm
  · left
    funext x
    have h := hp s x
    simpa [normCol,hn] using h
  · right
    funext x
    have h := hm s x
    simpa [normCol,hn] using h

private theorem normCol_value (P : Config 9 3) (s : Fin 9) (Q : Common.Partition 9)
    (hQ : IsPartition Q 3) (b : Bool) :
    SignedValue P (normCol s Q b)=TverbergSign P Q := by
  let f : ZMod 3 → ZMod 3 := fun x => if b then x-CanonColour Q s else -(x-CanonColour Q s)
  have hi : Function.Injective f := by
    intro x y h
    cases b <;> simpa [f] using h
  let e : Equiv.Perm (ZMod 3) := Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩
  have he : e ∘ CanonColour Q=normCol s Q b := rfl
  rw [←he,(Sierksma.signed_determinant_colour_invariant P (CanonColour Q) e).2.1]
  simp [TverbergSign,hQ]

private theorem normCol_diff (s : Fin 9) (Q : Common.Partition 9) (b : Bool) (u v : Fin 9) :
    normCol s Q b v-normCol s Q b u =
      if b then CanonColour Q v-CanonColour Q u else -(CanonColour Q v-CanonColour Q u) := by
  cases b <;> simp only [normCol,Bool.false_eq_true,if_false,if_true] <;> ring

theorem Sierksma.L15.normalized_colour_sum (P : Config 9 3) (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) :
    TwistPolynomial (TverbergSign P) pi c = SplitSign pi *
      ∑ col : Fin 9 → ZMod 3, if col (pi 0)=0 then SignedValue P col *
        ∏ i : Fin 4, (col (pi (SplitPosV i))-col (pi (SplitPosU i))-c i) else 0 := by
  classical
  let s : Fin 9 := pi 0
  let w (col : Fin 9 → ZMod 3) : ZMod 3 :=
    ∏ i : Fin 4, (col (pi (SplitPosV i))-col (pi (SplitPosU i))-c i)
  let T := (Finset.univ : Finset (Fin 9 → ZMod 3)).filter
    (fun col => col s=0 ∧ Function.Surjective col)
  let f (a : Common.Partition 9 × Bool) := normCol s a.1 a.2
  have part (a : Common.Partition 9 × Bool) (ha : a ∈ ((ThreePartitions 9).product (Finset.univ : Finset Bool))) : IsPartition a.1 3 := by
    have hh := (Finset.mem_product (s := ThreePartitions 9)
      (t := (Finset.univ : Finset Bool)) (p := a)).mp ha
    have ha' : a.1 ∈ ThreePartitions 9 := hh.1
    simpa only [ThreePartitions,Finset.mem_filter,Finset.mem_univ,true_and] using ha'
  have hbij : ∑ a ∈ ((ThreePartitions 9).product (Finset.univ : Finset Bool)), SignedValue P (f a) * w (f a) =
      ∑ col ∈ T, SignedValue P col * w col := by
    apply Finset.sum_bij (fun a _ => f a)
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        normCol_base s a.1 a.2,normCol_surj s a.1 (part a ha) a.2⟩
    · rintro ⟨Q,b⟩ ha ⟨Q',b'⟩ ha' he
      have hp := (respects_fibres Q (part (Q,b) ha) _ (normCol_respects s Q (part (Q,b) ha) b)).2
      have hp' := (respects_fibres Q' (part (Q',b') ha') _ (normCol_respects s Q' (part (Q',b') ha') b')).2
      change normCol s Q b=normCol s Q' b' at he
      have hQQ : Q=Q' := hp.symm.trans ((congrArg (ColoredBlocks Finset.univ) he).trans hp')
      subst Q'
      cases b <;> cases b'
      · rfl
      · exact False.elim (normCol_ne s Q (part (Q,false) ha) he.symm)
      · exact False.elim (normCol_ne s Q (part (Q,true) ha) he)
      · rfl
    · intro col hcol
      obtain ⟨_,hn,hs⟩ := Finset.mem_filter.mp hcol
      let Q := ColoredBlocks Finset.univ col
      have hQ := coloredBlocks_partition col hs
      have hr := coloredBlocks_respects col
      have hmem : Q ∈ ThreePartitions 9 := by
        change Q ∈ Finset.univ.filter (fun R => IsPartition R 3)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hQ⟩
      rcases normalized_form s Q hQ col hr hn with hp | hm
      · refine ⟨(Q,true),?_,?_⟩
        · change (Q,true) ∈ (ThreePartitions 9).product Finset.univ
          exact Finset.mem_product.mpr ⟨hmem,Finset.mem_univ _⟩
        · exact hp.symm
      · refine ⟨(Q,false),?_,?_⟩
        · change (Q,false) ∈ (ThreePartitions 9).product Finset.univ
          exact Finset.mem_product.mpr ⟨hmem,Finset.mem_univ _⟩
        · exact hm.symm
    · intro _ _; rfl
  have hexpand : ∑ Q ∈ ThreePartitions 9,
      TverbergSign P Q * ((∏ i : Fin 4, (EdgeDiff Q (SplitEdge pi i)-c i)) +
        (∏ i : Fin 4, (-EdgeDiff Q (SplitEdge pi i)-c i))) =
      ∑ a ∈ ((ThreePartitions 9).product (Finset.univ : Finset Bool)), SignedValue P (f a)*w (f a) := by
    calc
      _ = ∑ Q ∈ ThreePartitions 9, ∑ b : Bool, SignedValue P (f (Q,b))*w (f (Q,b)) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        have hpart : IsPartition Q 3 := (Finset.mem_filter.mp hQ).2
        rw [Fintype.sum_bool]
        simp only [f,normCol_value P s Q hpart,w,normCol_diff,Bool.false_eq_true,if_false,if_true,
          EdgeDiff,SplitEdge]
        ring
      _ = _ := (Finset.sum_product (ThreePartitions 9) (Finset.univ : Finset Bool)
        (fun a => SignedValue P (f a)*w (f a))).symm
  have hfilter : ∑ col ∈ T, SignedValue P col*w col =
      ∑ col : Fin 9 → ZMod 3, if col s=0 then SignedValue P col*w col else 0 := by
    rw [←Finset.sum_filter]
    apply Finset.sum_subset
    · intro col hcol
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hcol).2.1⟩
    · intro col hcol hn
      have hzero : SignedValue P col=0 := by
        by_contra hs
        apply hn
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hcol).2,signedValue_surj P col hs⟩
      simp [hzero]
  unfold TwistPolynomial
  exact congrArg (fun z : ZMod 3 => SplitSign pi*z) (hexpand.trans (hbij.trans hfilter))
end
end L15Source1

section L15Source2

section
open PLDegree
open scoped BigOperators
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

private theorem LibR_listSign_comp_perm_local {V : Type*} [LinearOrder V] {k : ℕ}
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

theorem LibR_solution {V : Type*} [LinearOrder V] {k : ℕ}
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
    rw [← hq,LibR_listSign_comp_perm_local _ (S.orderEmbOfFin hcard).injective q,hsorted,mul_one]
  have hftsign : listSign (f ∘ t)=(q.sign : ℤ)*listSign (f ∘ S.orderEmbOfFin hcard) := by
    rw [← hq,← Function.comp_assoc]
    exact LibR_listSign_comp_perm_local _ (hf.comp (S.orderEmbOfFin hcard).injective) q
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
open PLDegree
open scoped BigOperators
set_option maxHeartbeats 800000

private theorem LibC_listSign_cons_local {V : Type*} [LinearOrder V] {k : ℕ} (y : V) (t : Fin k → V) :
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

theorem LibC_solution {V : Type*} [LinearOrder V] {k : ℕ}
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
  rw [LibC_listSign_cons_local]
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

theorem LibS_solution {V : Type*} [LinearOrder V] {k : ℕ}
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
end

section
open Common Sierksma
set_option maxRecDepth 2048
theorem LibH_solution : ∀ c : ZMod 3, let H : Fin 6 → ZMod 3 × ZMod 3 := fun a =>
    (if a.val%2=0 then (a.val/2 : ℕ) else (a.val/2+1 : ℕ), c-1+(a.val/2 : ℕ));
    (∀ a, (H a).2-(H a).1 ≠ c) ∧ (∀ a b, H a=H b → a=b) ∧
    (∀ u v : ZMod 3, v-u ≠ c → ∃ a, H a=(u,v)) ∧
    (∀ a, chi ((H a).2-(H a).1-c)=if a.val%2=0 then -1 else 1) := by
  decide +kernel
end

section
open Common Sierksma
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem LibT_twist_base_finite_bijection_local (c : Fin 4 → ZMod 3) :
    (∀ v : Fin 27, TwistPhi 1 c v.val < 27) ∧
    (∀ u v : Fin 27, TwistPhi 1 c u.val = TwistPhi 1 c v.val → u=v) ∧
    (∀ j : Fin 27, ∃ v : Fin 27, TwistPhi 1 c v.val=j.val) := by
  let F (d : ZMod 3) (a : Fin 6) : ℕ :=
    3*(a.val%2)+(if a.val%2=0 then a.val/2 else (d-1+(a.val/2 : ℕ)).val)
  have hf : ∀ d : ZMod 3,
      (∀ a : Fin 6, F d a<6) ∧
      (∀ a b : Fin 6, F d a=F d b → a=b) ∧
      (∀ r : Fin 6, ∃ a : Fin 6, F d a=r.val) := by decide +kernel
  have hphi (i : Fin 4) (a : Fin 6) :
      TwistPhi 1 c (6*i.val+a.val)=6*i.val+3+F (c i) a := by
    fin_cases i <;> fin_cases a <;>
      simp [TwistPhi,SplitPosU,SplitPosV,F,Fin.coe_ofNat_eq_mod] <;> omega
  have hhex (v : Fin 27) (hv : v.val<24) :
      TwistPhi 1 c v.val=6*(v.val/6)+3+F (c ⟨v.val/6,by omega⟩) ⟨v.val%6,Nat.mod_lt _ (by omega)⟩ := by
    have he : v.val=6*(v.val/6)+v.val%6 := by omega
    conv_lhs => rw [he]
    exact hphi ⟨v.val/6,by omega⟩ ⟨v.val%6,Nat.mod_lt _ (by omega)⟩
  have hapex (v : Fin 27) (hv : ¬v.val<24) : TwistPhi 1 c v.val=v.val-24 := by
    simp [TwistPhi,hv,v.isLt]
  constructor
  · intro v
    by_cases hv : v.val<24
    · rw [hhex v hv]
      have hh := (hf (c ⟨v.val/6,by omega⟩)).1 ⟨v.val%6,Nat.mod_lt _ (by omega)⟩
      omega
    · rw [hapex v hv]; omega
  constructor
  · intro u v he
    by_cases hu : u.val<24 <;> by_cases hv : v.val<24
    · rw [hhex u hu,hhex v hv] at he
      have hfu := (hf (c ⟨u.val/6,by omega⟩)).1 ⟨u.val%6,Nat.mod_lt _ (by omega)⟩
      have hfv := (hf (c ⟨v.val/6,by omega⟩)).1 ⟨v.val%6,Nat.mod_lt _ (by omega)⟩
      have hdiv : u.val/6=v.val/6 := by omega
      have hi : (⟨u.val/6,by omega⟩ : Fin 4)=⟨v.val/6,by omega⟩ := Fin.ext hdiv
      rw [hi] at he
      have ha := (hf (c ⟨v.val/6,by omega⟩)).2.1
        ⟨u.val%6,Nat.mod_lt _ (by omega)⟩ ⟨v.val%6,Nat.mod_lt _ (by omega)⟩ (by omega)
      have hmod : u.val%6=v.val%6 := congrArg Fin.val ha
      apply Fin.ext
      omega
    · rw [hhex u hu,hapex v hv] at he
      omega
    · rw [hapex u hu,hhex v hv] at he
      omega
    · rw [hapex u hu,hapex v hv] at he
      apply Fin.ext
      omega
  · intro j
    by_cases hj : j.val<3
    · refine ⟨⟨24+j.val,by omega⟩,?_⟩
      rw [hapex _ (by simp <;> omega)]
      simp
    · let i : Fin 4 := ⟨(j.val-3)/6,by omega⟩
      let r : Fin 6 := ⟨(j.val-3)%6,Nat.mod_lt _ (by omega)⟩
      obtain ⟨a,ha⟩ := (hf (c i)).2.2 r
      refine ⟨⟨6*i.val+a.val,by omega⟩,?_⟩
      change TwistPhi 1 c (6*i.val+a.val)=j.val
      rw [hphi,ha]
      dsimp [i,r]
      omega

theorem LibT_solution (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) :
    Function.Bijective (TwistPhi pi c) ∧
    (∀ v, TwistPhi pi c (ShiftVertex v)=ColorShiftVertex (TwistPhi pi c v)) := by
  let V (p : Equiv.Perm (Fin 9)) (v : ℕ) : ℕ :=
    if h : v<27 then 3*(p ⟨v/3,by omega⟩).val+v%3 else v
  have hVlabel (p : Equiv.Perm (Fin 9)) (u : Fin 9) (a : ℕ) (ha : a<3) :
      V p (3*u.val+a)=3*(p u).val+a := by
    have hlt : 3*u.val+a<27 := by omega
    have hdiv : (⟨(3*u.val+a)/3,by omega⟩ : Fin 9)=u := by
      apply Fin.ext
      change (3*u.val+a)/3=u.val
      omega
    have hmod : (3*u.val+a)%3=a := by omega
    simp [V,hlt,hdiv,hmod]
  have hVinverse (p : Equiv.Perm (Fin 9)) (v : ℕ) : V p.symm (V p v)=v := by
    by_cases hv : v<27
    · let u : Fin 9 := ⟨v/3,by omega⟩
      have he : v=3*u.val+v%3 := by dsimp [u]; omega
      conv_lhs => rw [he]
      rw [hVlabel p u (v%3) (Nat.mod_lt _ (by omega)),
        hVlabel p.symm (p u) (v%3) (Nat.mod_lt _ (by omega))]
      simp only [Equiv.symm_apply_apply]
      omega
    · simp [V,hv]
  have hVbij : Function.Bijective (V pi) := by
    refine ⟨?_,?_⟩
    · exact (show Function.LeftInverse (V pi.symm) (V pi) from hVinverse pi).injective
    · apply Function.RightInverse.surjective (g := V pi.symm)
      intro v
      simpa using hVinverse pi.symm v
  have hfactor (v : ℕ) : TwistPhi pi c v=V pi (TwistPhi 1 c v) := by
    by_cases hv : v<27
    · interval_cases v
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 0) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 0) (((c 0-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 0) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 0) (((c 0-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 0) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 0) (((c 0-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 1) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 1) (((c 1-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 1) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 1) (((c 1-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 1) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 1) (((c 1-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 2) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 2) (((c 2-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 2) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 2) (((c 2-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 2) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 2) (((c 2-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 3) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 3) (((c 3-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 3) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 3) (((c 3-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 3) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 3) (((c 3-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi 0 ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi 0 ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi 0 ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
    · simp [TwistPhi,V,hv,show ¬v<24 by omega]
  obtain ⟨hbounds,hinj,hsurj⟩ := LibT_twist_base_finite_bijection_local c
  have hbase : Function.Bijective (TwistPhi 1 c) := by
    constructor
    · intro u v he
      by_cases hu : u<27
      · by_cases hv : v<27
        · exact congrArg Fin.val (hinj ⟨u,hu⟩ ⟨v,hv⟩ he)
        · have hsmall := hbounds ⟨u,hu⟩
          change TwistPhi 1 c u<27 at hsmall
          have hfix : TwistPhi 1 c v=v := by simp [TwistPhi,hv,show ¬v<24 by omega]
          rw [hfix] at he
          omega
      · by_cases hv : v<27
        · have hsmall := hbounds ⟨v,hv⟩
          change TwistPhi 1 c v<27 at hsmall
          have hfix : TwistPhi 1 c u=u := by simp [TwistPhi,hu,show ¬u<24 by omega]
          rw [hfix] at he
          omega
        · simpa [TwistPhi,hu,hv,show ¬u<24 by omega,show ¬v<24 by omega] using he
    · intro j
      by_cases hj : j<27
      · obtain ⟨v,hv⟩ := hsurj ⟨j,hj⟩
        exact ⟨v.val,hv⟩
      · exact ⟨j,by simp [TwistPhi,hj,show ¬j<24 by omega]⟩
  have hbaseShift : ∀ v, TwistPhi 1 c (ShiftVertex v)=ColorShiftVertex (TwistPhi 1 c v) := by
    have hfinite : ∀ c : Fin 4 → ZMod 3, ∀ v : Fin 27,
        TwistPhi 1 c (ShiftVertex v.val)=ColorShiftVertex (TwistPhi 1 c v.val) := by
      decide +kernel
    intro v
    by_cases hv : v<27
    · exact hfinite c ⟨v,hv⟩
    · simp [ShiftVertex,ColorShiftVertex,TwistPhi,hv,show ¬v<24 by omega]
  have hClabel (u : Fin 9) (a : ℕ) (ha : a<3) :
      ColorShiftVertex (3*u.val+a)=3*u.val+(a+1)%3 := by
    have hlt : 3*u.val+a<27 := by omega
    have hdiv : (3*u.val+a)/3=u.val := by omega
    have hmod : (3*u.val+a)%3=a := by omega
    simp [ColorShiftVertex,hlt,hdiv,hmod]
  have hVshift (v : ℕ) : V pi (ColorShiftVertex v)=ColorShiftVertex (V pi v) := by
    by_cases hv : v<27
    · let u : Fin 9 := ⟨v/3,by omega⟩
      have hr : v%3<3 := Nat.mod_lt _ (by omega)
      have he : v=3*u.val+v%3 := by dsimp [u]; omega
      rw [he,hClabel u _ hr,hVlabel pi _ _ (Nat.mod_lt _ (by omega)),
        hVlabel pi u _ hr,hClabel (pi u) _ hr]
    · simp [V,ColorShiftVertex,hv]
  constructor
  · have hf : TwistPhi pi c=V pi ∘ TwistPhi 1 c := funext hfactor
    rw [hf]
    exact hVbij.comp hbase
  · intro v
    rw [hfactor,hbaseShift,hVshift,← hfactor]
end

section
open scoped BigOperators
open Common PLDegree Sierksma
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
noncomputable section
attribute [local instance] Classical.propDecidable

private def HC (c : ZMod 3) (a : Fin 6) : ZMod 3 × ZMod 3 :=
  (if a.val%2=0 then (a.val/2 : ℕ) else (a.val/2+1 : ℕ),c-1+(a.val/2 : ℕ))
private def FC (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (a : Fin 4 → Fin 6)
    (v : Fin 9) : ZMod 3 :=
  let r := pi.symm v
  if h : r.val=0 then 0 else
    let i : Fin 4 := ⟨(r.val-1)/2,by omega⟩
    if r.val%2=1 then (HC (c i) (a i)).1 else (HC (c i) (a i)).2
private def SP (a : Fin 4 → Fin 6) : Equiv.Perm (Fin 9) :=
  (if (a 0).val%2=1 then Equiv.swap 1 2 else 1) *
  (if (a 1).val%2=1 then Equiv.swap 3 4 else 1) *
  (if (a 2).val%2=1 then Equiv.swap 5 6 else 1) *
  (if (a 3).val%2=1 then Equiv.swap 7 8 else 1)
private def Label (col : Fin 9 → ZMod 3) (v : Fin 9) : ℕ := 3*v.val+(col v).val

private theorem FC_zero (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (a : Fin 4 → Fin 6) :
    FC pi c a (pi 0)=0 := by simp [FC]
private theorem FC_U (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (a : Fin 4 → Fin 6) (i : Fin 4) :
    FC pi c a (pi (SplitPosU i))=(HC (c i) (a i)).1 := by
  fin_cases i <;> simp [FC,SplitPosU,Fin.coe_ofNat_eq_mod]
private theorem FC_V (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (a : Fin 4 → Fin 6) (i : Fin 4) :
    FC pi c a (pi (SplitPosV i))=(HC (c i) (a i)).2 := by
  fin_cases i <;> simp [FC,SplitPosV,Fin.coe_ofNat_eq_mod]
private theorem HC_sign (c : ZMod 3) (a : Fin 6) :
    chi ((HC c a).2-(HC c a).1-c)=if a.val%2=0 then -1 else 1 := by
  exact (LibH_solution c).2.2.2 a
private theorem label_mono (col : Fin 9 → ZMod 3) : StrictMono (Label col) := by
  intro u v huv
  have hu := ZMod.val_lt (col u)
  have hv := ZMod.val_lt (col v)
  change 3*u.val+(col u).val < 3*v.val+(col v).val
  change u.val<v.val at huv
  omega

private theorem SP_zero (a : Fin 4 → Fin 6) : SP a 0=0 := by
  simp only [SP,Equiv.Perm.mul_apply]
  split_ifs <;> simp [Equiv.swap_apply_def]
private theorem SP_U (a : Fin 4 → Fin 6) (i : Fin 4) :
    SP a (SplitPosU i)=if (a i).val%2=0 then SplitPosU i else SplitPosV i := by
  fin_cases i <;> simp only [SP,Equiv.Perm.mul_apply,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod]
  all_goals split_ifs <;> simp_all [Equiv.swap_apply_def] <;> omega
private theorem SP_V (a : Fin 4 → Fin 6) (i : Fin 4) :
    SP a (SplitPosV i)=if (a i).val%2=0 then SplitPosV i else SplitPosU i := by
  fin_cases i <;> simp only [SP,Equiv.Perm.mul_apply,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod]
  all_goals split_ifs <;> simp_all [Equiv.swap_apply_def] <;> omega
private theorem mapped_tuple (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (a : Fin 4 → Fin 6) :
    TwistPhi pi c ∘ Fin.cons 24 (HexTuple a) = Label (FC pi c a) ∘ (pi*SP a) := by
  have hcases : ∀ a : Fin 6, a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by decide +kernel
  funext r
  fin_cases r
  · simp [Function.comp_apply,Equiv.Perm.mul_apply,SP_zero,TwistPhi,Label,FC_zero]
  · have hSP := SP_U a 0
    change TwistPhi pi c (HexTuple a 0)=Label (FC pi c a) (pi (SP a 1))
    have hpos : (1 : Fin 9)=SplitPosU 0 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 0) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]
  · have hSP := SP_V a 0
    change TwistPhi pi c (HexTuple a 1)=Label (FC pi c a) (pi (SP a 2))
    have hpos : (2 : Fin 9)=SplitPosV 0 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 0) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]
  · have hSP := SP_U a 1
    change TwistPhi pi c (HexTuple a 2)=Label (FC pi c a) (pi (SP a 3))
    have hpos : (3 : Fin 9)=SplitPosU 1 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 1) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]
  · have hSP := SP_V a 1
    change TwistPhi pi c (HexTuple a 3)=Label (FC pi c a) (pi (SP a 4))
    have hpos : (4 : Fin 9)=SplitPosV 1 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 1) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]
  · have hSP := SP_U a 2
    change TwistPhi pi c (HexTuple a 4)=Label (FC pi c a) (pi (SP a 5))
    have hpos : (5 : Fin 9)=SplitPosU 2 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 2) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]
  · have hSP := SP_V a 2
    change TwistPhi pi c (HexTuple a 5)=Label (FC pi c a) (pi (SP a 6))
    have hpos : (6 : Fin 9)=SplitPosV 2 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 2) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]
  · have hSP := SP_U a 3
    change TwistPhi pi c (HexTuple a 6)=Label (FC pi c a) (pi (SP a 7))
    have hpos : (7 : Fin 9)=SplitPosU 3 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 3) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]
  · have hSP := SP_V a 3
    change TwistPhi pi c (HexTuple a 7)=Label (FC pi c a) (pi (SP a 8))
    have hpos : (8 : Fin 9)=SplitPosV 3 := by rfl
    rw [hpos,hSP]
    rcases hcases (a 3) with ha | ha | ha | ha | ha | ha <;>
      simp [HexTuple,TwistPhi,Label,FC,HC,ha,SplitPosU,SplitPosV,
        Fin.coe_ofNat_eq_mod,ZMod.val_natCast,ZMod.val_ofNat,ZMod.val_one_eq_one_mod]

private theorem SP_sign (a : Fin 4 → Fin 6) :
    (SP a).sign = ∏ i : Fin 4, (if (a i).val%2=0 then (1 : ℤˣ) else -1) := by
  simp only [SP,map_mul]
  rw [Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.prod_univ_succ]
  simp only [Fin.prod_univ_zero,Fin.isValue,mul_one]
  split_ifs <;> simp_all [Equiv.Perm.sign_swap] <;> omega

private theorem mapped_facet (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (a : Fin 4 → Fin 6) :
    listedFace (TwistPhi pi c ∘ Fin.cons 24 (HexTuple a)) =
      Finsupp.single (ColorFacet (FC pi c a))
        ((pi.sign : ℤ)*∏ i : Fin 4, chi (FC pi c a (pi (SplitPosV i))-FC pi c a (pi (SplitPosU i))-c i)) := by
  rw [mapped_tuple]
  have hsign : listSign (Label (FC pi c a))=1 := by
    have hno (ij : Fin 9 × Fin 9) : ¬(ij.1 < ij.2 ∧ ij.2 < ij.1) := by omega
    simp [listSign,(label_mono _).lt_iff_lt,hno]
  have hcoef : listSign (Label (FC pi c a) ∘ (pi*SP a)) =
      (pi.sign : ℤ)*∏ i : Fin 4, chi (FC pi c a (pi (SplitPosV i))-FC pi c a (pi (SplitPosU i))-c i) := by
    rw [LibS_solution _ (label_mono _).injective (pi*SP a),hsign,mul_one,
      map_mul,Units.val_mul,SP_sign,Units.coe_prod]
    simp_rw [FC_V,FC_U,HC_sign]
    have hlocal (i : Fin 4) : ((if (a i).val%2=0 then (1:ℤˣ) else -1) : ℤ)=
        -(if (a i).val%2=0 then -1 else 1) := by
      split_ifs <;> norm_num
    congr 1
    calc
      _ = ∏ i : Fin 4, -(if (a i).val%2=0 then (-1:ℤ) else 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases h : (a i).val%2=0 <;> simp [h]
      _ = _ := by rw [Finset.prod_neg]; norm_num
  have himage : Finset.univ.image (Label (FC pi c a) ∘ (pi*SP a))=ColorFacet (FC pi c a) := by
    unfold ColorFacet
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply]
    constructor
    · rintro ⟨r,hr⟩
      exact ⟨(pi*SP a) r,hr⟩
    · rintro ⟨r,hr⟩
      exact ⟨(pi*SP a).symm r,by simpa [Label] using hr⟩
  unfold listedFace
  congr 1
  · apply Finset.ext
    intro v
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using Finset.ext_iff.mp himage v

private def Allowed (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (col : Fin 9 → ZMod 3) : Prop :=
  col (pi 0)=0 ∧ ∀ i, col (pi (SplitPosV i))-col (pi (SplitPosU i)) ≠ c i
private theorem FC_allowed (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (a : Fin 4 → Fin 6) :
    Allowed pi c (FC pi c a) := by
  refine ⟨FC_zero pi c a,?_⟩
  intro i
  rw [FC_U,FC_V]
  exact (LibH_solution (c i)).1 (a i)
private theorem FC_inj (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) : Function.Injective (FC pi c) := by
  intro a b h
  funext i
  apply (LibH_solution (c i)).2.1
  apply Prod.ext
  · simpa only [FC_U,HC] using congrFun h (pi (SplitPosU i))
  · simpa only [FC_V,HC] using congrFun h (pi (SplitPosV i))
private theorem FC_surj (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3)
    (col : Fin 9 → ZMod 3) (hc : Allowed pi c col) : ∃ a, FC pi c a=col := by
  classical
  have ha (i : Fin 4) : ∃ a : Fin 6, HC (c i) a=(col (pi (SplitPosU i)),col (pi (SplitPosV i))) :=
    (LibH_solution (c i)).2.2.1 _ _ (hc.2 i)
  let a := fun i => Classical.choose (ha i)
  refine ⟨a,?_⟩
  have hU (i : Fin 4) : FC pi c a (pi (SplitPosU i))=col (pi (SplitPosU i)) := by
    rw [FC_U]
    exact congrArg Prod.fst (Classical.choose_spec (ha i))
  have hV (i : Fin 4) : FC pi c a (pi (SplitPosV i))=col (pi (SplitPosV i)) := by
    rw [FC_V]
    exact congrArg Prod.snd (Classical.choose_spec (ha i))
  funext v
  obtain ⟨r,rfl⟩ := pi.surjective v
  fin_cases r
  · change FC pi c a (pi 0)=col (pi 0)
    rw [FC_zero]
    exact hc.1.symm
  · exact hU 0
  · exact hV 0
  · exact hU 1
  · exact hV 1
  · exact hU 2
  · exact hV 2
  · exact hU 3
  · exact hV 3
private def CTerm (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (col : Fin 9 → ZMod 3) : Chain ℕ :=
  Finsupp.single (ColorFacet col) ((pi.sign : ℤ)*∏ i : Fin 4,
    chi (col (pi (SplitPosV i))-col (pi (SplitPosU i))-c i))
private theorem color_chain_filter (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) :
    ColorChain pi c = ∑ col ∈ Finset.univ.filter (Allowed pi c), CTerm pi c col := by
  classical
  rw [Finset.sum_filter]
  unfold ColorChain
  apply Finset.sum_congr rfl
  intro col hcol
  by_cases h0 : col (pi 0)=0
  · by_cases hall : ∀ i, col (pi (SplitPosV i))-col (pi (SplitPosU i)) ≠ c i
    · simp [Allowed,h0,hall,CTerm]
    · obtain ⟨i,hi⟩ := not_forall.mp hall
      have hz : ∏ j : Fin 4, chi (col (pi (SplitPosV j))-col (pi (SplitPosU j))-c j)=0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [chi,not_ne_iff.mp hi]
      simp [Allowed,h0,hall,CTerm,hz]
  · simp [Allowed,h0]
private def RelabelHom (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun := relabel f
  map_zero' := by simp [relabel]
  map_add' c d := Finsupp.sum_add_index' (fun s => zero_smul ℤ _)
    (fun s a b => add_smul a b _)

theorem Sierksma.twist_chain_orientation (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3) :
    relabel (TwistPhi pi c) (EngineCone 0)=ColorChain pi c := by
  classical
  have hexinj (a : Fin 4 → Fin 6) : Function.Injective (HexTuple a) := by

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

  have hexapex (a : Fin 4 → Fin 6) (i : Fin 8) : HexTuple a i ≠ 24 := by
    have hl := (a ⟨i.val/2,by omega⟩).isLt
    have hm := Nat.mod_lt ((a ⟨i.val/2,by omega⟩).val+1) (by omega : 0<6)
    dsimp [HexTuple]
    split_ifs <;> omega
  have hsum : EngineCone 0=∑ a : Fin 4 → Fin 6, listedFace (Fin.cons 24 (HexTuple a)) := by
    change ConeOperator 24 HexCycle=_
    rw [HexCycle,map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact LibC_solution 24 (HexTuple a) (hexinj a) (hexapex a)
  change RelabelHom (TwistPhi pi c) (EngineCone 0)=ColorChain pi c
  rw [hsum,map_sum,color_chain_filter]
  apply Finset.sum_bij (fun a _ => FC pi c a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,FC_allowed pi c a⟩
  · intro a ha b hb h
    exact FC_inj pi c h
  · intro col hcol
    obtain ⟨a,ha⟩ := FC_surj pi c col (Finset.mem_filter.mp hcol).2
    exact ⟨a,Finset.mem_univ _,ha⟩
  · intro a ha
    change relabel (TwistPhi pi c) (listedFace (Fin.cons 24 (HexTuple a)))=CTerm pi c (FC pi c a)
    have hi : Function.Injective (Fin.cons 24 (HexTuple a)) := by
      apply Fin.cons_injective_iff.mpr
      exact ⟨by rintro ⟨i,hi⟩; exact hexapex a i hi,hexinj a⟩
    rw [LibR_solution _ hi _ (LibT_solution pi c).1.1]
    exact mapped_facet pi c a

end
end
end L15Source2

section L15Source3
open Common Sierksma
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem twist_base_finite_bijection_local (c : Fin 4 → ZMod 3) :
    (∀ v : Fin 27, TwistPhi 1 c v.val < 27) ∧
    (∀ u v : Fin 27, TwistPhi 1 c u.val = TwistPhi 1 c v.val → u=v) ∧
    (∀ j : Fin 27, ∃ v : Fin 27, TwistPhi 1 c v.val=j.val) := by
  let F (d : ZMod 3) (a : Fin 6) : ℕ :=
    3*(a.val%2)+(if a.val%2=0 then a.val/2 else (d-1+(a.val/2 : ℕ)).val)
  have hf : ∀ d : ZMod 3,
      (∀ a : Fin 6, F d a<6) ∧
      (∀ a b : Fin 6, F d a=F d b → a=b) ∧
      (∀ r : Fin 6, ∃ a : Fin 6, F d a=r.val) := by decide +kernel
  have hphi (i : Fin 4) (a : Fin 6) :
      TwistPhi 1 c (6*i.val+a.val)=6*i.val+3+F (c i) a := by
    fin_cases i <;> fin_cases a <;>
      simp [TwistPhi,SplitPosU,SplitPosV,F,Fin.coe_ofNat_eq_mod] <;> omega
  have hhex (v : Fin 27) (hv : v.val<24) :
      TwistPhi 1 c v.val=6*(v.val/6)+3+F (c ⟨v.val/6,by omega⟩) ⟨v.val%6,Nat.mod_lt _ (by omega)⟩ := by
    have he : v.val=6*(v.val/6)+v.val%6 := by omega
    conv_lhs => rw [he]
    exact hphi ⟨v.val/6,by omega⟩ ⟨v.val%6,Nat.mod_lt _ (by omega)⟩
  have hapex (v : Fin 27) (hv : ¬v.val<24) : TwistPhi 1 c v.val=v.val-24 := by
    simp [TwistPhi,hv,v.isLt]
  constructor
  · intro v
    by_cases hv : v.val<24
    · rw [hhex v hv]
      have hh := (hf (c ⟨v.val/6,by omega⟩)).1 ⟨v.val%6,Nat.mod_lt _ (by omega)⟩
      omega
    · rw [hapex v hv]; omega
  constructor
  · intro u v he
    by_cases hu : u.val<24 <;> by_cases hv : v.val<24
    · rw [hhex u hu,hhex v hv] at he
      have hfu := (hf (c ⟨u.val/6,by omega⟩)).1 ⟨u.val%6,Nat.mod_lt _ (by omega)⟩
      have hfv := (hf (c ⟨v.val/6,by omega⟩)).1 ⟨v.val%6,Nat.mod_lt _ (by omega)⟩
      have hdiv : u.val/6=v.val/6 := by omega
      have hi : (⟨u.val/6,by omega⟩ : Fin 4)=⟨v.val/6,by omega⟩ := Fin.ext hdiv
      rw [hi] at he
      have ha := (hf (c ⟨v.val/6,by omega⟩)).2.1
        ⟨u.val%6,Nat.mod_lt _ (by omega)⟩ ⟨v.val%6,Nat.mod_lt _ (by omega)⟩ (by omega)
      have hmod : u.val%6=v.val%6 := congrArg Fin.val ha
      apply Fin.ext
      omega
    · rw [hhex u hu,hapex v hv] at he
      omega
    · rw [hapex u hu,hhex v hv] at he
      omega
    · rw [hapex u hu,hapex v hv] at he
      apply Fin.ext
      omega
  · intro j
    by_cases hj : j.val<3
    · refine ⟨⟨24+j.val,by omega⟩,?_⟩
      rw [hapex _ (by simp <;> omega)]
      simp
    · let i : Fin 4 := ⟨(j.val-3)/6,by omega⟩
      let r : Fin 6 := ⟨(j.val-3)%6,Nat.mod_lt _ (by omega)⟩
      obtain ⟨a,ha⟩ := (hf (c i)).2.2 r
      refine ⟨⟨6*i.val+a.val,by omega⟩,?_⟩
      change TwistPhi 1 c (6*i.val+a.val)=j.val
      rw [hphi,ha]
      dsimp [i,r]
      omega

theorem Sierksma.twist_label_symmetry (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) :
    Function.Bijective (TwistPhi pi c) ∧
    (∀ v, TwistPhi pi c (ShiftVertex v)=ColorShiftVertex (TwistPhi pi c v)) := by
  let V (p : Equiv.Perm (Fin 9)) (v : ℕ) : ℕ :=
    if h : v<27 then 3*(p ⟨v/3,by omega⟩).val+v%3 else v
  have hVlabel (p : Equiv.Perm (Fin 9)) (u : Fin 9) (a : ℕ) (ha : a<3) :
      V p (3*u.val+a)=3*(p u).val+a := by
    have hlt : 3*u.val+a<27 := by omega
    have hdiv : (⟨(3*u.val+a)/3,by omega⟩ : Fin 9)=u := by
      apply Fin.ext
      change (3*u.val+a)/3=u.val
      omega
    have hmod : (3*u.val+a)%3=a := by omega
    simp [V,hlt,hdiv,hmod]
  have hVinverse (p : Equiv.Perm (Fin 9)) (v : ℕ) : V p.symm (V p v)=v := by
    by_cases hv : v<27
    · let u : Fin 9 := ⟨v/3,by omega⟩
      have he : v=3*u.val+v%3 := by dsimp [u]; omega
      conv_lhs => rw [he]
      rw [hVlabel p u (v%3) (Nat.mod_lt _ (by omega)),
        hVlabel p.symm (p u) (v%3) (Nat.mod_lt _ (by omega))]
      simp only [Equiv.symm_apply_apply]
      omega
    · simp [V,hv]
  have hVbij : Function.Bijective (V pi) := by
    refine ⟨?_,?_⟩
    · exact (show Function.LeftInverse (V pi.symm) (V pi) from hVinverse pi).injective
    · apply Function.RightInverse.surjective (g := V pi.symm)
      intro v
      simpa using hVinverse pi.symm v
  have hfactor (v : ℕ) : TwistPhi pi c v=V pi (TwistPhi 1 c v) := by
    by_cases hv : v<27
    · interval_cases v
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 0) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 0) (((c 0-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 0) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 0) (((c 0-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 0) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 0) (((c 0-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 1) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 1) (((c 1-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 1) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 1) (((c 1-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 1) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 1) (((c 1-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 2) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 2) (((c 2-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 2) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 2) (((c 2-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 2) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 2) (((c 2-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 3) ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 3) (((c 3-1+(0:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 3) ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 3) (((c 3-1+(1:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosU 3) ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi (SplitPosV 3) (((c 3-1+(2:ZMod 3)) : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi 0 ((0 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi 0 ((1 : ZMod 3).val) (ZMod.val_lt _)).symm
      · simpa [TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
          (hVlabel pi 0 ((2 : ZMod 3).val) (ZMod.val_lt _)).symm
    · simp [TwistPhi,V,hv,show ¬v<24 by omega]
  obtain ⟨hbounds,hinj,hsurj⟩ := twist_base_finite_bijection_local c
  have hbase : Function.Bijective (TwistPhi 1 c) := by
    constructor
    · intro u v he
      by_cases hu : u<27
      · by_cases hv : v<27
        · exact congrArg Fin.val (hinj ⟨u,hu⟩ ⟨v,hv⟩ he)
        · have hsmall := hbounds ⟨u,hu⟩
          change TwistPhi 1 c u<27 at hsmall
          have hfix : TwistPhi 1 c v=v := by simp [TwistPhi,hv,show ¬v<24 by omega]
          rw [hfix] at he
          omega
      · by_cases hv : v<27
        · have hsmall := hbounds ⟨v,hv⟩
          change TwistPhi 1 c v<27 at hsmall
          have hfix : TwistPhi 1 c u=u := by simp [TwistPhi,hu,show ¬u<24 by omega]
          rw [hfix] at he
          omega
        · simpa [TwistPhi,hu,hv,show ¬u<24 by omega,show ¬v<24 by omega] using he
    · intro j
      by_cases hj : j<27
      · obtain ⟨v,hv⟩ := hsurj ⟨j,hj⟩
        exact ⟨v.val,hv⟩
      · exact ⟨j,by simp [TwistPhi,hj,show ¬j<24 by omega]⟩
  have hbaseShift : ∀ v, TwistPhi 1 c (ShiftVertex v)=ColorShiftVertex (TwistPhi 1 c v) := by
    have hfinite : ∀ c : Fin 4 → ZMod 3, ∀ v : Fin 27,
        TwistPhi 1 c (ShiftVertex v.val)=ColorShiftVertex (TwistPhi 1 c v.val) := by
      decide +kernel
    intro v
    by_cases hv : v<27
    · exact hfinite c ⟨v,hv⟩
    · simp [ShiftVertex,ColorShiftVertex,TwistPhi,hv,show ¬v<24 by omega]
  have hClabel (u : Fin 9) (a : ℕ) (ha : a<3) :
      ColorShiftVertex (3*u.val+a)=3*u.val+(a+1)%3 := by
    have hlt : 3*u.val+a<27 := by omega
    have hdiv : (3*u.val+a)/3=u.val := by omega
    have hmod : (3*u.val+a)%3=a := by omega
    simp [ColorShiftVertex,hlt,hdiv,hmod]
  have hVshift (v : ℕ) : V pi (ColorShiftVertex v)=ColorShiftVertex (V pi v) := by
    by_cases hv : v<27
    · let u : Fin 9 := ⟨v/3,by omega⟩
      have hr : v%3<3 := Nat.mod_lt _ (by omega)
      have he : v=3*u.val+v%3 := by dsimp [u]; omega
      rw [he,hClabel u _ hr,hVlabel pi _ _ (Nat.mod_lt _ (by omega)),
        hVlabel pi u _ hr,hClabel (pi u) _ hr]
    · simp [V,ColorShiftVertex,hv]
  constructor
  · have hf : TwistPhi pi c=V pi ∘ TwistPhi 1 c := funext hfactor
    rw [hf]
    exact hVbij.comp hbase
  · intro v
    rw [hfactor,hbaseShift,hVshift,← hfactor]
end L15Source3

section L15Source4
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open Common Sierksma

private theorem testW_shift_local (P : Config 9 3) (v : Fin 9) (j : ZMod 3) :
    R8 (TestW P v j) = TestW P v (j+1) := by
  ext k
  have hc : ∀ j : ZMod 3, j=0 ∨ j=1 ∨ j=2 := by decide +kernel
  rcases hc j with rfl | rfl | rfl <;> fin_cases k <;>
    simp +decide [R8,TestW] <;> ring

private theorem target_test_map_label_local (P : Config 9 3) (v : Fin 9) (j : ZMod 3) :
    TargetTestMap P (3*v.val+j.val) = TestW P v j := by
  have hj : j.val<3 := ZMod.val_lt j
  have hlt : 3*v.val+j.val<27 := by omega
  have hdiv : (3*v.val+j.val)/3=v.val := by omega
  have hmod : (3*v.val+j.val)%3=j.val := by omega
  simp [TargetTestMap,hlt,hdiv,hmod]

private theorem Sierksma.twist_test_coordinates (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (P : Config 9 3)
    (v : ℕ) (hv : v<27) :
    EngineMap (TestParams P pi c) v=TargetTestMap P (TwistPhi pi c v) := by
  have hp (k : ℕ) (u : Fin 9) (j : ZMod 3) :
      RPower k (TestW P u j)=TestW P u (j+k) := by
    unfold RPower
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,testW_shift_local]
      push_cast
      congr 1
      ring
  interval_cases v
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 0)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 0)) ((c 0-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 0)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 0)) ((c 0-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 0)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 0)) ((c 0-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 1)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 1)) ((c 1-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 1)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 1)) ((c 1-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 1)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 1)) ((c 1-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 2)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 2)) ((c 2-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 2)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 2)) ((c 2-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 2)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 2)) ((c 2-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 3)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 3)) ((c 3-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 3)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 3)) ((c 3-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 3)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 3)) ((c 3-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi 0) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi 0) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi 0) (2 : ZMod 3)).symm
end L15Source4

section L15Source5
open Common PLDegree Sierksma

theorem Sierksma.twisted_hexagon_orientation (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3) :
    Function.Bijective (TwistPhi pi c) ∧
    (∀ v, TwistPhi pi c (ShiftVertex v)=ColorShiftVertex (TwistPhi pi c v)) ∧
    relabel (TwistPhi pi c) (EngineCone 0)=ColorChain pi c ∧
    (∀ P : Config 9 3, ∀ v : ℕ, v<27 →
      EngineMap (TestParams P pi c) v=TargetTestMap P (TwistPhi pi c v)) := by
  obtain ⟨hbij,hshift⟩ := Sierksma.twist_label_symmetry pi c
  exact ⟨hbij,hshift,Sierksma.twist_chain_orientation pi hpi c,
    fun P v hv => Sierksma.twist_test_coordinates pi c P v hv⟩
end L15Source5

section L15Source6
set_option autoImplicit false
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
end L15Source6

section L15Source7
open Common PLDegree Sierksma

theorem proof_Sierksma_twist_polynomial_cone_count (P : Config 9 3) (hP : P ∈ GenericLocus)
    (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3) :
    TwistPolynomial (TverbergSign P) pi c=(ConeCount (TestParams P pi c) 0 : ZMod 3) := by
  obtain ⟨hb,_,hc,hm⟩ := Sierksma.twisted_hexagon_orientation pi hpi c
  have heq : TargetTestMap P ∘ TwistPhi pi c = EngineMap (TestParams P pi c) := by
    funext v
    by_cases hv : v<27
    · exact (hm P v hv).symm
    · have hv24 : ¬v<24 := by omega
      simp [Function.comp_def,EngineMap,TwistPhi,TargetTestMap,hv,hv24]
  rw [Sierksma.L15.normalized_colour_sum,
    ← Sierksma.L15.color_chain_count, ← hc,
    PLDegree.signed_count_relabel _ hb.1,heq]
  rfl
end L15Source7
