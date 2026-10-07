import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_Amplification
import SierksmaLean.Definitions.Def_Sierksma_FractionalCover
import SierksmaLean.Definitions.Def_Sierksma_TwistedRealization
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
set_option autoImplicit false
open Common Sierksma
open scoped BigOperators
set_option maxRecDepth 4000
private theorem Sierksma.classification (P : Config 9 3) (hP : StrongGP P) (Q : Common.Partition 9) (hQ : BlocksOn Q (Q.biUnion id)) (hcard : Q.card = 3) (hz : HasCommonHull P Q) : Q ∈ Universe 3 := by
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

set_option maxHeartbeats 300000
set_option maxRecDepth 6000
open scoped BigOperators
open Common Sierksma

private theorem Sierksma.L11.face_exclusion (P : Config 9 3) (hP : StrongGP P) (A : Finset (Fin 9))
    (col : Fin 9 → ZMod 3) (hz : ColoredZero P A col) :
    A=Finset.univ ∧ ColoredBlocks A col ∈ Universe 3 := by
  classical
  obtain ⟨hne, z, hzh⟩ := (Sierksma.L11.zero_iff_common_hull P A col).mp hz
  have hQ : ColoredBlocks A col = Finset.univ.image (ColorBlock A col) := by
    apply Finset.filter_eq_self.mpr
    intro B hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact hne j
  have hmem (B : Finset (Fin 9)) : B ∈ ColoredBlocks A col ↔ ∃ j, B=ColorBlock A col j := by
    rw [hQ]; simp [eq_comm]
  have hunion : (ColoredBlocks A col).biUnion id = A := by
    ext v; simp only [Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨B, hB, hv⟩
      obtain ⟨j, rfl⟩ := (hmem B).mp hB
      exact (Finset.mem_filter.mp hv).1
    · intro hv
      refine ⟨ColorBlock A col (col v), (hmem _).mpr ⟨col v, rfl⟩, ?_⟩
      simp [ColorBlock, hv]
  have hinj : Function.Injective (ColorBlock A col) := by
    intro j k he
    obtain ⟨v, hv⟩ := hne j
    have hvk : v ∈ ColorBlock A col k := he ▸ hv
    exact (Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hvk).2
  have hcard : (ColoredBlocks A col).card=3 := by
    rw [hQ, Finset.card_image_of_injective _ hinj]
    norm_num
  have hbon : BlocksOn (ColoredBlocks A col) A := by
    refine ⟨?_, ?_, hunion⟩
    · intro B hB
      obtain ⟨j, rfl⟩ := (hmem B).mp hB
      exact ⟨hne j, Finset.filter_subset _ _⟩
    · intro B hB C hC hBC
      obtain ⟨j, rfl⟩ := (hmem B).mp hB
      obtain ⟨k, rfl⟩ := (hmem C).mp hC
      apply Finset.disjoint_left.mpr
      intro v hvj hvk
      have hjk : j=k := (Finset.mem_filter.mp hvj).2.symm.trans (Finset.mem_filter.mp hvk).2
      exact hBC (congrArg (ColorBlock A col) hjk)
  have hh : HasCommonHull P (ColoredBlocks A col) := by
    refine ⟨z, ?_⟩
    intro B hB; obtain ⟨j, rfl⟩ := (hmem B).mp hB; exact hzh j
  have hbon' : BlocksOn (ColoredBlocks A col) ((ColoredBlocks A col).biUnion id) := by
    rw [hunion]; exact hbon
  have hu := Sierksma.classification P hP (ColoredBlocks A col) hbon' hcard hh
  have hpu : IsPartition (ColoredBlocks A col) 3 := (Finset.mem_filter.mp hu).2.1
  exact ⟨hunion.symm.trans hpu.1.2.2, hu⟩

set_option autoImplicit false
open Common Sierksma
open scoped BigOperators

private theorem Sierksma.g1_polynomial_affine_gp (P : Config 9 3) (h : G1Polynomial P) : AffineGP P := by
  classical
  have h4 (a : Fin 4 → Fin 9) (ha : Function.Injective a) :
      AffineIndependent ℝ (fun i => P (a i)) := by
    let M : Matrix (Fin 4) (Fin 4) ℝ := fun i j => LiftCoord P (a i) j.val
    have hind : LinearIndependent ℝ (fun i => M i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero (h a ha)
    rw [affineIndependent_iff]
    intro s w hs hw
    have hm : ∑ i ∈ s, w i • M i = 0 := by
      ext j
      by_cases hj : j.val < 3
      · have he := congrFun hw ⟨j.val, hj⟩
        simpa [M, LiftCoord, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he
      · simpa [M, LiftCoord, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs
    exact (linearIndependent_iff'.mp hind) s w hm
  intro A hA
  obtain ⟨B, hAB, hBu, hB⟩ := Finset.exists_subsuperset_card_eq
    (show A ⊆ Finset.univ from Finset.subset_univ A) hA
    (show 4 ≤ (Finset.univ : Finset (Fin 9)).card by decide)
  let e : B ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using hB)
  let a : Fin 4 → Fin 9 := fun i => (e.symm i).val
  have ha : Function.Injective a := Subtype.val_injective.comp e.symm.injective
  have hBi : AffineIndependent ℝ (fun v : B => P v.val) := by
    convert (h4 a ha).comp_embedding e.toEmbedding using 1
    ext v
    simp [a, Function.comp_def]
  let f : A ↪ B := ⟨fun v => ⟨v.val, hAB v.property⟩, by
    intro v v' he
    exact Subtype.ext (congrArg (fun z : B => z.val) he)⟩
  exact hBi.comp_embedding f

set_option autoImplicit false
open Common Sierksma Set
open scoped BigOperators

private theorem Sierksma.generic_locus_strong_gp : ∀ P ∈ GenericLocus, StrongGP P := by
  classical
  intro P hP
  refine ⟨Sierksma.g1_polynomial_affine_gp P hP.1, ?_⟩
  have henumerate (T : Finset (Fin 9)) (hT : T.card = 3) :
      ∃ t : Fin 3 → Fin 9, Function.Injective t ∧ Finset.univ.image t = T := by
    let e : T ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hT)
    let t : Fin 3 → Fin 9 := fun i => (e.symm i).val
    refine ⟨t, Subtype.val_injective.comp e.symm.injective, ?_⟩
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (e.symm i).property
    · intro hv
      refine Finset.mem_image.mpr ⟨e ⟨v, hv⟩, Finset.mem_univ _, ?_⟩
      simp [t]
  have hcalc (t : Fin 3 → Fin 9) (q : Fin 3 → ℝ) : TripleDet P t q =
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 1-P (t 0) 1)*q 2 -
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 2-P (t 0) 2)*q 1 -
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 0-P (t 0) 0)*q 2 +
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 2-P (t 0) 2)*q 0 +
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 0-P (t 0) 0)*q 1 -
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 1-P (t 0) 1)*q 0 := by
    change Matrix.det (Matrix.of ![P (t 1)-P (t 0), P (t 2)-P (t 0), q]) = _
    rw [Matrix.det_fin_three]
    simp [Matrix.of_apply, Matrix.vecTail, Matrix.vecHead, Pi.sub_apply]
  have hplane (t : Fin 3 → Fin 9) (z : Fin 3 → ℝ)
      (hz : z ∈ affineSpan ℝ (range (fun i => P (t i)))) :
      TripleDet P t (z-P (t 0)) = 0 := by
    let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := {
      toFun := fun q => TripleDet P t q
      map_add' := by
        intro q r
        simp only [hcalc, Pi.add_apply]
        ring
      map_smul' := by
        intro c q
        simp only [hcalc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    let F : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ :=
      L.toAffineMap - AffineMap.const ℝ (Fin 3 → ℝ) (L (P (t 0)))
    have hbase : ∀ i : Fin 3, F (P (t i)) = 0 := by
      intro i
      change L (P (t i)) - L (P (t 0)) = 0
      rw [← L.map_sub]
      change TripleDet P t (P (t i)-P (t 0)) = 0
      rw [hcalc]
      fin_cases i <;> simp [Pi.sub_apply] <;> ring
    have he : (range (fun i => P (t i))).EqOn F (AffineMap.const ℝ (Fin 3 → ℝ) 0) := by
      rintro x ⟨i, rfl⟩
      exact hbase i
    have hz' := AffineMap.eqOn_affineSpan he hz
    change L z - L (P (t 0)) = 0 at hz'
    rw [← L.map_sub] at hz'
    exact hz'
  intro E T T' hE hT hT' hET hET' hTT'
  rintro ⟨z, hzE, hzT, hzT'⟩
  have hep : ∃ u v : Fin 9, u < v ∧ E = {u,v} := by
    obtain ⟨u,v,hne,hEq⟩ := Finset.card_eq_two.mp hE
    rcases lt_or_gt_of_ne hne with huv | hvu
    · exact ⟨u,v,huv,hEq⟩
    · exact ⟨v,u,hvu,by simpa [Finset.pair_comm] using hEq⟩
  obtain ⟨u,v,huv,hEq⟩ := hep
  obtain ⟨t, ht, hti⟩ := henumerate T hT
  obtain ⟨t', ht', hti'⟩ := henumerate T' hT'
  let e : Edge 9 := (u,v)
  have hETt : Disjoint (Endpoints e) (Finset.univ.image t) := by
    simpa [e, Endpoints, hEq, hti] using hET
  have hETt' : Disjoint (Endpoints e) (Finset.univ.image t') := by
    simpa [e, Endpoints, hEq, hti'] using hET'
  have hTtt' : Disjoint (Finset.univ.image t) (Finset.univ.image t') := by
    simpa [hti,hti'] using hTT'
  have hQ : QPoly P e t t' ≠ 0 := hP.2.1 e huv t t' ht ht' hETt hETt' hTtt'
  have hTset (s : Fin 3 → Fin 9) (S : Finset (Fin 9)) (hi : Finset.univ.image s = S) :
      range (fun i => P (s i)) = P '' (S : Set (Fin 9)) := by
    rw [← hi]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i, rfl⟩
  have hzE' : z ∈ affineSpan ℝ ({P u,P v} : Set (Fin 3 → ℝ)) := by
    simpa only [hEq, Finset.coe_pair, Set.image_insert_eq, Set.image_singleton] using hzE
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp hzE'
  have hroot (s : Fin 3 → Fin 9)
      (hz : z ∈ affineSpan ℝ (range (fun i => P (s i)))) :
      r * TripleDet P s (P v-P u) + TripleDet P s (P u-P (s 0)) = 0 := by
    have hp := hplane s z hz
    have he : z-P (s 0) = r • (P v-P u) + (P u-P (s 0)) := by
      rw [← hr, AffineMap.lineMap_apply_module']
      abel
    rw [he] at hp
    simp only [hcalc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp ⊢
    linear_combination hp
  have hrT := hroot t (by rwa [hTset t T hti])
  have hrT' := hroot t' (by rwa [hTset t' T' hti'])
  apply hQ
  change TripleDet P t (P v-P u) * TripleDet P t' (P u-P (t' 0)) -
      TripleDet P t' (P v-P u) * TripleDet P t (P u-P (t 0)) = 0
  linear_combination (TripleDet P t (P v-P u))*hrT' -
    (TripleDet P t' (P v-P u))*hrT

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

set_option maxHeartbeats 800000
set_option maxRecDepth 6000
open scoped BigOperators
open Common Sierksma

theorem Sierksma.L11.support_iff (P : Config 9 3) (hP : P ∈ GenericLocus) (Q : Common.Partition 9) :
    TverbergSign P Q ≠ 0 ↔ Q ∈ TverbergPartitions 3 P := by
  classical
  have hstrong : StrongGP P := Sierksma.generic_locus_strong_gp P hP
  have sign_nonzero (r : ℝ) (hr : r ≠ 0) : (((SignType.sign r : SignType) : ℤ) : ZMod 3) ≠ 0 := by
    rcases lt_or_gt_of_ne hr with hn | hp
    · rw [sign_neg hn]; norm_num
    · rw [sign_pos hp]; norm_num
  let col := CanonColour Q
  let M := SignMatrix P col
  let b : Fin 9 → ℝ := Pi.single 8 1
  let lam := Matrix.vecMul b M⁻¹
  have row (v : Fin 9) (k : Fin 8) : M v k.castSucc = TestW P v (col v) k := by
    have hk : k.val ≠ 8 := by omega
    simp [M, SignMatrix, SignRow, TestW, hk]
  have eqs (w : Fin 9 → ℝ) : Matrix.vecMul w M = b ↔
      (∑ v, w v)=1 ∧ (∑ v, w v • TestW P v (col v))=0 := by
    have endeq : Matrix.vecMul w M 8 = ∑ v, w v := by
      simp [Matrix.vecMul, dotProduct, M, SignMatrix, SignRow]
    have coord (k : Fin 8) : Matrix.vecMul w M k.castSucc =
        (∑ v, w v • TestW P v (col v)) k := by
      simp only [Matrix.vecMul, dotProduct, row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro he
      refine ⟨?_, ?_⟩
      · have hh := congrFun he 8; simpa [endeq, b] using hh
      · funext k
        have hh := congrFun he k.castSucc
        have hk : k.castSucc ≠ (8 : Fin 9) := by intro he; have := congrArg Fin.val he; dsimp at this; omega
        simpa [coord, b, Pi.single_apply, hk] using hh
    · rintro ⟨h1, h0⟩
      funext j
      by_cases hj : j=(8:Fin 9)
      · subst j; simp [endeq,h1,b]
      · have hj8 : j.val < 8 := by
          have hlt := j.isLt
          have hn : j.val ≠ 8 := by
            intro hn
            apply hj
            apply Fin.ext
            simpa using hn
          omega
        have hjk : j=(⟨j.val,hj8⟩:Fin 8).castSucc := rfl
        rw [hjk,coord,h0]
        have hkne : (⟨j.val,hj8⟩:Fin 8).castSucc ≠ (8:Fin 9) := by simpa only [← hjk] using hj
        simp [b,Pi.single_apply,hkne,Ne.symm hkne]
        all_goals assumption
  have lam_sol (hd : M.det ≠ 0) : Matrix.vecMul lam M = b := by
    dsimp [lam]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hd), Matrix.vecMul_one]
  have pos_of_zero (w : Fin 9 → ℝ) (hw : ∀ v, 0 ≤ w v)
      (h1 : (∑ v, w v)=1) (h0 : (∑ v, w v • TestW P v (col v))=0) : ∀ v, 0 < w v := by
    let A := Finset.univ.filter (fun v => 0 < w v)
    have hs : ∀ v, v ∉ A → w v=0 := by
      intro v hv
      have hn : ¬ 0 < w v := by simpa [A] using hv
      exact le_antisymm (le_of_not_gt hn) (hw v)
    have he := (Sierksma.L11.face_exclusion P hstrong A col ⟨w,hw,hs,h1,h0⟩).1
    intro v
    have hv : v ∈ A := he ▸ Finset.mem_univ v
    exact (Finset.mem_filter.mp hv).2
  have hull_bridge (hQ : IsPartition Q 3) : HasCommonHull P Q ↔ ColoredCommonHull P Finset.univ col := by
    have hr : Respects Q col := Sierksma.canon_colour_respects Q hQ
    have hne : ∀ B : Q, B.val.Nonempty := fun B => (hQ.1.1 B.val B.property).1
    choose v hv using hne
    have fibre (B : Q) : ColorBlock Finset.univ col (col (v B)) = B.val := by
      ext u
      simp only [ColorBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hc
        obtain ⟨C,hC,hu,hvC⟩ := (hr u (v B)).mp hc
        by_cases he : C=B.val
        · simpa [he] using hu
        · have hd := hQ.1.2.1 C hC B.val B.property he
          exact False.elim ((Finset.disjoint_left.mp hd) hvC (hv B))
      · intro hu
        exact (hr u (v B)).mpr ⟨B.val,B.property,hu,hv B⟩
    have hi : Function.Injective (fun B : Q => col (v B)) := by
      intro B C he; change col (v B)=col (v C) at he; apply Subtype.ext
      rw [← fibre B, ← fibre C, he]
    have hcard : Fintype.card Q = Fintype.card (ZMod 3) := by simpa using hQ.2
    have hsur := ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,hcard⟩).2
    constructor
    · rintro ⟨z,hz⟩
      refine ⟨?_,⟨z,?_⟩⟩
      · intro j; obtain ⟨B,hB⟩ := hsur j
        rw [← hB,fibre]; exact (hQ.1.1 B.val B.property).1
      · intro j; obtain ⟨B,hB⟩ := hsur j
        rw [← hB,fibre]; exact hz B.val B.property
    · rintro ⟨_,z,hz⟩
      refine ⟨z,?_⟩
      intro B hB
      simpa only [fibre ⟨B,hB⟩] using hz (col (v ⟨B,hB⟩))
  constructor
  · intro hs
    have hQ : IsPartition Q 3 := by
      by_contra hn; simp [TverbergSign,hn] at hs
    have hsv : SignedValue P col ≠ 0 := by simpa [TverbergSign,hQ,col] using hs
    have hc : M.det ≠ 0 ∧ ∀ v, 0 < lam v := by
      change (SignMatrix P col).det ≠ 0 ∧ ∀ v, 0 < Matrix.vecMul (Pi.single (8:Fin 9) (1:ℝ)) (SignMatrix P col)⁻¹ v
      by_contra hn
      have heq : SignedValue P col=0 := by rw [SignedValue, if_neg hn]
      exact hsv heq
    have hz : ColoredZero P Finset.univ col := by
      have he := (eqs lam).mp (lam_sol hc.1)
      exact ⟨lam,fun v => (hc.2 v).le,by simp,he.1,he.2⟩
    have hh := (hull_bridge hQ).mpr ((Sierksma.L11.zero_iff_common_hull P _ col).mp hz)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hQ,hh⟩
  · intro hT
    obtain ⟨hQ,hh⟩ := (Finset.mem_filter.mp hT).2
    have hbon : BlocksOn Q (Q.biUnion id) := by rw [hQ.1.2.2]; exact hQ.1
    have hu := Sierksma.classification P hstrong Q hbon hQ.2 hh
    have hd : M.det ≠ 0 := (hP.2.2 Q hu).1
    obtain ⟨w,hw,hws,h1,h0⟩ := (Sierksma.L11.zero_iff_common_hull P _ col).mpr ((hull_bridge hQ).mp hh)
    have hwM := (eqs w).mpr ⟨h1,h0⟩
    have hwlam : w=lam := by
      have hi := Matrix.vecMul_injective_of_isUnit (M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd))
      apply hi
      change Matrix.vecMul w M = Matrix.vecMul lam M
      rw [hwM,lam_sol hd]
    have hl : ∀ v, 0 < lam v := by rw [← hwlam]; exact pos_of_zero w hw h1 h0
    have hsv : SignedValue P col ≠ 0 := by
      rw [SignedValue, if_pos ⟨hd,hl⟩]
      exact sign_nonzero M.det hd
    simpa [TverbergSign,hQ,col] using hsv

open scoped BigOperators
open Common Sierksma

theorem Sierksma.L11.large_block_determinant_zero (P : Config 9 3) (col : Fin 9 → ZMod 3)
    (h : ∃ j : ZMod 3, 5 ≤ (ColorBlock Finset.univ col j).card) :
    (SignMatrix P col).det=0 := by
  classical
  obtain ⟨j, hj⟩ := h
  let B := ColorBlock Finset.univ col j
  let f : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ) :=
    { toFun := fun x k =>
        if h8 : k.val = 8 then x 3
        else if hk : k.val < 4 then
          if j=0 then -x ⟨k.val,hk⟩ else if j=1 then x ⟨k.val,hk⟩ else 0
        else if j=0 then -x ⟨k.val-4,by have hk9 := k.isLt; omega⟩
          else if j=1 then 0 else x ⟨k.val-4,by have hk9 := k.isLt; omega⟩
      map_add' := by intro x y; ext k; dsimp; split_ifs <;> simp [add_comm]
      map_smul' := by intro a x; ext k; dsimp; split_ifs <;> simp [mul_neg] }
  have he (v : B) : f (fun k : Fin 4 => LiftCoord P v.val k.val) = SignMatrix P col v.val := by
    have hc : col v.val=j := (Finset.mem_filter.mp v.property).2
    ext k
    dsimp [f, SignMatrix, SignRow]
    split_ifs <;> simp_all [LiftCoord]
  by_contra hn
  have hr := Matrix.linearIndependent_rows_of_det_ne_zero hn
  have hs : LinearIndependent ℝ (fun v : B => SignMatrix P col v.val) :=
    hr.comp Subtype.val Subtype.val_injective
  have hl : LinearIndependent ℝ (fun v : B => (fun k : Fin 4 => LiftCoord P v.val k.val)) := by
    apply LinearIndependent.of_comp f
    have heq : f ∘ (fun v : B => (fun k : Fin 4 => LiftCoord P v.val k.val)) = (fun v : B => SignMatrix P col v.val) := by
      funext v; exact he v
    rw [heq]; exact hs
  have hb := hl.fintype_card_le_finrank
  have hc : Fintype.card B = B.card := Fintype.card_coe _
  have hdim : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
  change 5 ≤ B.card at hj
  omega

theorem proof_Sierksma_test_map_zero_equivalence :
    (∀ P : Config 9 3, ∀ A : Finset (Fin 9), ∀ col : Fin 9 → ZMod 3,
      ColoredZero P A col ↔ ColoredCommonHull P A col) ∧
    (∀ P : Config 9 3, StrongGP P → ∀ A : Finset (Fin 9), ∀ col : Fin 9 → ZMod 3,
      ColoredZero P A col → A=Finset.univ ∧ ColoredBlocks A col ∈ Universe 3) ∧
    (∀ P : Config 9 3, ∀ col : Fin 9 → ZMod 3,
      (∃ j : ZMod 3, 5 ≤ (ColorBlock Finset.univ col j).card) →
        (SignMatrix P col).det=0) ∧
    (∀ P ∈ GenericLocus, ∀ Q : Common.Partition 9,
      TverbergSign P Q ≠ 0 ↔ Q ∈ TverbergPartitions 3 P)  := by
  exact ⟨(fun P A col => Sierksma.L11.zero_iff_common_hull P A col),
    (fun P hP A col hz => Sierksma.L11.face_exclusion P hP A col hz),
    (fun P col h => Sierksma.L11.large_block_determinant_zero P col h),
    (fun P hP Q => Sierksma.L11.support_iff P hP Q)⟩
