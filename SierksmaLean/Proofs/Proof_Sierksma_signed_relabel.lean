import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_RelabelConstraint
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
import SierksmaLean.Definitions.Def_Sierksma_SplitCoordinate
set_option autoImplicit false
open Sierksma

private theorem Sierksma.partition_relabel_inverse_type {n : ℕ}
    (p : Equiv.Perm (Fin n)) (Q : Common.Partition n) :
    Relabel p.symm (Relabel p Q) = Q ∧
      (Relabel p Q).val.map Finset.card = Q.val.map Finset.card := by
  classical
  have hinv (A : Common.Block n) : (A.image p).image p.symm = A := by
    simp [Finset.image_image, Function.comp_def]
  have hinj : Function.Injective (fun A : Common.Block n => A.image p) := by
    intro A B h
    have hh := congrArg (Finset.image p.symm) h
    simpa only [hinv] using hh
  have hcard (A : Common.Block n) : (A.image p).card = A.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => p.injective h)
  constructor
  · simp only [Relabel, Finset.image_image, Function.comp_def, hinv, Finset.image_id']
  · unfold Relabel
    rw [Finset.image_val_of_injOn (fun _ _ _ _ h => hinj h), Multiset.map_map]
    change Q.val.map (fun A => (A.image p).card) = Q.val.map Finset.card
    exact congrArg (fun f : Common.Block n → ℕ => Q.val.map f) (funext hcard)

set_option autoImplicit false
open Common Sierksma
noncomputable section

theorem Sierksma.is_partition_relabel {n r : ℕ} (π : Equiv.Perm (Fin n)) (Q : Common.Partition n) :
    Common.IsPartition (Relabel π Q) r ↔ Common.IsPartition Q r := by
  classical
  have forward (p : Equiv.Perm (Fin n)) (R : Common.Partition n)
      (hR : IsPartition R r) : IsPartition (Relabel p R) r := by
    obtain ⟨⟨hne, hd, hu⟩, hc⟩ := hR
    have hcard : (Relabel p R).card = R.card := by
      have h := congrArg Multiset.card (partition_relabel_inverse_type p R).2
      simpa only [Multiset.card_map, Finset.card] using h
    refine ⟨⟨?_, ?_, ?_⟩, hcard.trans hc⟩
    · intro A hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      exact ⟨(hne B hB).1.image p, Finset.subset_univ _⟩
    · intro A hA B hB hAB
      obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
      apply (Finset.disjoint_image p.injective).mpr
      exact hd A' hA' B' hB' (fun h => hAB (congrArg (Finset.image p) h))
    · apply Finset.eq_univ_iff_forall.mpr
      intro x
      have hx : p.symm x ∈ R.biUnion id := by rw [hu]; exact Finset.mem_univ _
      obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
      apply Finset.mem_biUnion.mpr
      refine ⟨A.image p, Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨p.symm x, hxA, p.apply_symm_apply x⟩
  constructor
  · intro h
    have h' := forward π.symm (Relabel π Q) h
    simpa only [(partition_relabel_inverse_type π Q).1] using h'
  · exact forward π Q

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
open Sierksma

theorem Sierksma.respects_relabel {n : ℕ}
    (p : Equiv.Perm (Fin n)) (Q : Common.Partition n) (col : Fin n → ZMod 3) :
    Respects (Relabel p Q) col ↔ Respects Q (fun x => col (p x)) := by
  classical
  have hparts (u v : Fin n) :
      (∃ B ∈ Relabel p Q, p u ∈ B ∧ p v ∈ B) ↔
      (∃ A ∈ Q, u ∈ A ∧ v ∈ A) := by
    constructor
    · rintro ⟨B, hB, hu, hv⟩
      rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
      rcases Finset.mem_image.mp hu with ⟨u', hu', heu⟩
      rcases Finset.mem_image.mp hv with ⟨v', hv', hev⟩
      have eu : u' = u := p.injective heu
      have ev : v' = v := p.injective hev
      exact ⟨A, hA, eu ▸ hu', ev ▸ hv'⟩
    · rintro ⟨A, hA, hu, hv⟩
      exact ⟨A.image p, Finset.mem_image.mpr ⟨A, hA, rfl⟩,
        Finset.mem_image.mpr ⟨u, hu, rfl⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  constructor
  · intro h u v
    exact (h (p u) (p v)).trans (hparts u v)
  · intro h u v
    have hh := (h (p.symm u) (p.symm v)).trans (hparts (p.symm u) (p.symm v)).symm
    simpa only [Equiv.apply_symm_apply] using hh

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

set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
noncomputable section

theorem Sierksma.respects_even_products {n : ℕ} (Q : Common.Partition n) (c d : Fin n → ZMod 3)
    (hc : Respects Q c) (hd : Respects Q d) :
    (∀ e f : Edge n, (d e.2 - d e.1) * (d f.2 - d f.1) =
      (c e.2 - c e.1) * (c f.2 - c f.1)) ∧
    (∀ E : Fin 4 → Edge n, (∏ i, (d (E i).2 - d (E i).1)) =
      ∏ i, (c (E i).2 - c (E i).1)) := by
  classical
  have hdir : (∀ x y, d y - d x = c y - c x) ∨
      (∀ x y, d y - d x = -(c y - c x)) := by
    by_cases hn : ∃ u v, c u ≠ c v
    · obtain ⟨u, v, huv⟩ := hn
      exact respects_two_orientations Q c d hc hd u v huv
    · left
      intro x y
      have hxy : c x = c y := by by_contra h; exact hn ⟨x, y, h⟩
      have hdxy := (hd x y).mpr ((hc x y).mp hxy)
      simp only [hdxy, hxy, sub_self]
  rcases hdir with h | h
  · constructor
    · intro e f; rw [h, h]
    · intro E; simp_rw [h]
  · constructor
    · intro e f; rw [h, h]; ring
    · intro E
      simp_rw [h]
      rw [Finset.prod_neg]
      norm_num

set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
noncomputable section

theorem Sierksma.edge_diff_relabel_even {n : ℕ} (π : Equiv.Perm (Fin n)) (Q : Common.Partition n)
    (hQ : IsPartition Q 3) :
    (∀ e f : Edge n, EdgeDiff (Relabel π Q) (π e.1, π e.2) *
      EdgeDiff (Relabel π Q) (π f.1, π f.2) = EdgeDiff Q e * EdgeDiff Q f) ∧
    (∀ E : Fin 4 → Edge n, (∏ i, EdgeDiff (Relabel π Q) (π (E i).1, π (E i).2)) =
      ∏ i, EdgeDiff Q (E i)) := by
  classical
  have hc := canon_colour_respects Q hQ
  have hR : IsPartition (Relabel π Q) 3 := (is_partition_relabel π Q).mpr hQ
  have hd := (respects_relabel π Q (CanonColour (Relabel π Q))).mp
    (canon_colour_respects (Relabel π Q) hR)
  have h := respects_even_products Q (CanonColour Q)
    (fun x => CanonColour (Relabel π Q) (π x)) hc hd
  constructor
  · intro e f
    exact h.1 e f
  · intro E
    exact h.2 E

set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
noncomputable section

theorem Sierksma.signed_system_unordered_pairs (y : Common.Partition 9 → ZMod 3) (hy : SignedSystem y)
    (e f : Edge 9) (hdis : Disjoint (Endpoints e) (Endpoints f)) :
    ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q e * EdgeDiff Q f = 0 := by
  classical
  by_cases heq : e.1 = e.2
  · simp [EdgeDiff, heq]
  by_cases hfq : f.1 = f.2
  · simp [EdgeDiff, hfq]
  have hflip (Q : Common.Partition 9) (a : Edge 9) :
      EdgeDiff Q a = -EdgeDiff Q (a.2, a.1) := by
    simp only [EdgeDiff]
    ring
  have ordered (a : Edge 9) (ha : a.1 < a.2)
      (hD : Disjoint (Endpoints a) (Endpoints f)) :
      ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q a * EdgeDiff Q f = 0 := by
    by_cases hf : f.1 < f.2
    · exact hy.2.1 a f ha hf hD
    · have hf' : f.2 < f.1 := lt_of_le_of_ne (le_of_not_gt hf) (Ne.symm hfq)
      have hD' : Disjoint (Endpoints a) (Endpoints (f.2, f.1)) := by
        simpa only [Endpoints, Finset.pair_comm] using hD
      have h := hy.2.1 a (f.2, f.1) ha hf' hD'
      calc
        _ = -(∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q a * EdgeDiff Q (f.2, f.1)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro Q hQ
          rw [hflip Q f]
          ring
        _ = 0 := by rw [h, neg_zero]
  by_cases he : e.1 < e.2
  · exact ordered e he hdis
  · have he' : e.2 < e.1 := lt_of_le_of_ne (le_of_not_gt he) (Ne.symm heq)
    have hD' : Disjoint (Endpoints (e.2, e.1)) (Endpoints f) := by
      simpa only [Endpoints, Finset.pair_comm] using hdis
    have h := ordered (e.2, e.1) he' hD'
    calc
      _ = -(∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (e.2, e.1) * EdgeDiff Q f) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [hflip Q e]
        ring
      _ = 0 := by rw [h, neg_zero]

open Common Sierksma
set_option autoImplicit false
private theorem Sierksma.split_edges_pairwise_disjoint (σ : Equiv.Perm (Fin 9)) (i j : Fin 4) (hij : i ≠ j) :
    Disjoint (Endpoints (SplitEdge σ i)) (Endpoints (SplitEdge σ j)) := by
  have hpos : ∀ i j : Fin 4, i ≠ j →
      SplitPosU i ≠ SplitPosU j ∧ SplitPosU i ≠ SplitPosV j ∧
      SplitPosV i ≠ SplitPosU j ∧ SplitPosV i ≠ SplitPosV j := by decide
  rcases hpos i j hij with ⟨huu, huv, hvu, hvv⟩
  simp only [Endpoints, SplitEdge, Finset.disjoint_insert_left,
    Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton,
    not_or, σ.injective.ne_iff]
  exact ⟨⟨huu, huv⟩, hvu, hvv⟩
open scoped BigOperators
open Common Sierksma
set_option autoImplicit false

private theorem Sierksma.splitting_of_matching (M : Finset (Edge 9)) (hM : IsMatching M) (hc : M.card = 4) :
    ∃ σ : Equiv.Perm (Fin 9), IsSplitting σ ∧
      ∀ e : Edge 9, e ∈ M ↔ ∃ i : Fin 4, SplitEdge σ i = e := by
  classical
  have hi : Set.InjOn (fun e : Edge 9 => e.1) M := by
    intro e he f hf hef
    by_contra hne
    exact Finset.disjoint_left.mp (hM.2 e he f hf hne)
      (show e.1 ∈ Endpoints e from by simp [Endpoints])
      (show e.1 ∈ Endpoints f from by simp [Endpoints, ← hef])
  let L : Finset (Fin 9) := M.image Prod.fst
  have hL : L.card = 4 := (Finset.card_image_of_injOn hi).trans hc
  let a : Fin 4 → Fin 9 := L.orderEmbOfFin hL
  have ha (i : Fin 4) : a i ∈ L := (L.orderIsoOfFin hL i).property
  have hex (i : Fin 4) : ∃ e ∈ M, e.1 = a i := Finset.mem_image.mp (ha i)
  let E : Fin 4 → Edge 9 := fun i => (hex i).choose
  have hE (i : Fin 4) : E i ∈ M := (hex i).choose_spec.1
  have hEa (i : Fin 4) : (E i).1 = a i := (hex i).choose_spec.2
  have hEinj : Function.Injective E := by
    intro i j h
    apply (L.orderEmbOfFin hL).injective
    change a i = a j
    rw [← hEa i, ← hEa j]
    exact congrArg Prod.fst h
  have hsep (i j : Fin 4) (hij : i ≠ j) :
      (E i).1 ≠ (E j).1 ∧ (E i).1 ≠ (E j).2 ∧
      (E i).2 ≠ (E j).1 ∧ (E i).2 ≠ (E j).2 := by
    have hd := hM.2 (E i) (hE i) (E j) (hE j) (hEinj.ne hij)
    simpa only [Endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or, and_assoc] using hd
  have hcard : (M.biUnion Endpoints).card = 8 := by
    rw [Finset.card_biUnion hM.2]
    have h2 : ∀ e ∈ M, (Endpoints e).card = 2 := by
      intro e he
      simp [Endpoints, (hM.1 e he).ne]
    calc
      (∑ e ∈ M, (Endpoints e).card) = ∑ e ∈ M, 2 := Finset.sum_congr rfl h2
      _ = 8 := by simp [hc]
  obtain ⟨s, hs, hsnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (M.biUnion Endpoints).card < (Finset.univ : Finset (Fin 9)).card by
      rw [hcard]; decide)
  have hssep (i : Fin 4) : s ≠ (E i).1 ∧ s ≠ (E i).2 := by
    have hn : s ∉ Endpoints (E i) := by
      intro h
      exact hsnot (Finset.mem_biUnion.mpr ⟨E i, hE i, h⟩)
    simpa only [Endpoints, Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  let l : List (Fin 9) := [s, (E 0).1, (E 0).2, (E 1).1, (E 1).2,
    (E 2).1, (E 2).2, (E 3).1, (E 3).2]
  have hl : l.Nodup := by
    simp [l, List.nodup_cons, hssep 0, hssep 1, hssep 2, hssep 3,
      hsep 0 1 (by decide), hsep 0 2 (by decide), hsep 0 3 (by decide),
      hsep 1 2 (by decide), hsep 1 3 (by decide), hsep 2 3 (by decide),
      (hM.1 (E 0) (hE 0)).ne, (hM.1 (E 1) (hE 1)).ne,
      (hM.1 (E 2) (hE 2)).ne, (hM.1 (E 3) (hE 3)).ne]
  let f : Fin 9 → Fin 9 := fun i => l[i.val]'(by simpa [l] using i.isLt)
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact (hl.getElem_inj_iff).mp h
  let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hσu (i : Fin 4) : σ (SplitPosU i) = (E i).1 := by fin_cases i <;> rfl
  have hσv (i : Fin 4) : σ (SplitPosV i) = (E i).2 := by fin_cases i <;> rfl
  have hedge (i : Fin 4) : SplitEdge σ i = E i := by
    exact Prod.ext (hσu i) (hσv i)
  refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
  · intro i
    simpa only [hσu i, hσv i] using hM.1 (E i) (hE i)
  · intro i j hij
    rw [hσu i, hσu j, hEa i, hEa j]
    exact (L.orderEmbOfFin hL).strictMono hij
  · intro e
    constructor
    · intro he
      have hem : e.1 ∈ L := Finset.mem_image.mpr ⟨e, he, rfl⟩
      obtain ⟨i, hia⟩ := (L.orderIsoOfFin hL).surjective ⟨e.1, hem⟩
      refine ⟨i, (hedge i).trans (hi (hE i) he ?_)⟩
      exact (hEa i).trans (congrArg Subtype.val hia)
    · rintro ⟨i, rfl⟩
      rw [hedge i]
      exact hE i
open Common Sierksma
set_option autoImplicit false

theorem Sierksma.split_normalization (σ : Equiv.Perm (Fin 9)) :
    ∃ τ : Equiv.Perm (Fin 9), IsSplitting τ ∧
      ∃ p : Equiv.Perm (Fin 4), ∃ f : Fin 4 → Equiv.Perm (Fin 2),
        σ 0 = τ 0 ∧ ∀ i b, σ (SplitCoordinate (Sum.inr (i, b))) =
          τ (SplitCoordinate (Sum.inr (p i, f i b))) := by
  classical
  have hune : ∀ i : Fin 4, SplitPosU i ≠ SplitPosV i := by decide
  have hzero : ∀ i : Fin 4, (0 : Fin 9) ≠ SplitPosU i ∧ (0 : Fin 9) ≠ SplitPosV i := by decide
  have huinj : Function.Injective SplitPosU := by decide
  have hcu (i : Fin 4) : SplitCoordinate (Sum.inr (i, 0)) = SplitPosU i := by
    fin_cases i <;> rfl
  have hcv (i : Fin 4) : SplitCoordinate (Sum.inr (i, 1)) = SplitPosV i := by
    fin_cases i <;> rfl
  let E : Fin 4 → Edge 9 := fun i =>
    (min (σ (SplitPosU i)) (σ (SplitPosV i)),
      max (σ (SplitPosU i)) (σ (SplitPosV i)))
  have hEn (i : Fin 4) : Endpoints (E i) = Endpoints (SplitEdge σ i) := by
    by_cases hl : σ (SplitPosU i) ≤ σ (SplitPosV i)
    · simp [E, Endpoints, SplitEdge, min_eq_left hl, max_eq_right hl]
    · have hl' : σ (SplitPosV i) ≤ σ (SplitPosU i) := le_of_not_ge hl
      simp [E, Endpoints, SplitEdge, min_eq_right hl', max_eq_left hl',
        Finset.pair_comm]
  have hEinj : Function.Injective E := by
    intro i j hij
    by_contra hne
    have hd := Sierksma.split_edges_pairwise_disjoint σ i j hne
    have hm : σ (SplitPosU i) ∈ Endpoints (SplitEdge σ i) := by simp [Endpoints, SplitEdge]
    have hm' : σ (SplitPosU i) ∈ Endpoints (SplitEdge σ j) := by
      rw [← hEn j, ← hij, hEn i]
      exact hm
    exact Finset.disjoint_left.mp hd hm hm'
  let M : Finset (Edge 9) := Finset.univ.image E
  have hM : IsMatching M := by
    constructor
    · intro e he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      change min (σ (SplitPosU i)) (σ (SplitPosV i)) <
        max (σ (SplitPosU i)) (σ (SplitPosV i))
      exact min_lt_max.mpr (σ.injective.ne (hune i))
    · intro e he e' he' hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he'
      rw [hEn i, hEn j]
      apply Sierksma.split_edges_pairwise_disjoint σ i j
      intro h
      exact hne (congrArg E h)
  have hc : M.card = 4 := by simp [M, Finset.card_image_of_injective _ hEinj]
  obtain ⟨τ, hτ, hedge⟩ := Sierksma.splitting_of_matching M hM hc
  have hex (i : Fin 4) : ∃ j : Fin 4, SplitEdge τ j = E i :=
    (hedge (E i)).mp (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let J : Fin 4 → Fin 4 := fun i => (hex i).choose
  have hJ (i : Fin 4) : SplitEdge τ (J i) = E i := (hex i).choose_spec
  have hJinj : Function.Injective J := by
    intro i j hij
    apply hEinj
    rw [← hJ i, ← hJ j, hij]
  let p : Equiv.Perm (Fin 4) := Equiv.ofBijective J ⟨hJinj, Finite.surjective_of_injective hJinj⟩
  let f : Fin 4 → Equiv.Perm (Fin 2) := fun i =>
    if σ (SplitPosU i) < σ (SplitPosV i) then Equiv.refl _ else Equiv.swap 0 1
  have hsnot : σ 0 ∉ M.biUnion Endpoints := by
    intro h
    obtain ⟨e, he, hmem⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    rw [hEn i] at hmem
    have : σ 0 ∉ Endpoints (SplitEdge σ i) := by
      simpa only [Endpoints, SplitEdge, Finset.mem_insert, Finset.mem_singleton,
        σ.injective.eq_iff, not_or] using hzero i
    exact this hmem
  have hsingleton : σ 0 = τ 0 := by
    obtain ⟨x, hx⟩ := τ.surjective (σ 0)
    have hpos : ∀ x : Fin 9, x = 0 ∨ ∃ i : Fin 4, x = SplitPosU i ∨ x = SplitPosV i := by decide
    rcases hpos x with rfl | ⟨i, rfl | rfl⟩
    · exact hx.symm
    · exfalso
      exact hsnot (Finset.mem_biUnion.mpr ⟨SplitEdge τ i,
        (hedge _).mpr ⟨i, rfl⟩, by simp [Endpoints, SplitEdge, ← hx]⟩)
    · exfalso
      exact hsnot (Finset.mem_biUnion.mpr ⟨SplitEdge τ i,
        (hedge _).mpr ⟨i, rfl⟩, by simp [Endpoints, SplitEdge, ← hx]⟩)
  refine ⟨τ, hτ, p, f, hsingleton, ?_⟩
  intro i b
  have ht : SplitEdge τ (p i) = E i := hJ i
  by_cases hl : σ (SplitPosU i) < σ (SplitPosV i)
  · have hleft : τ (SplitPosU (p i)) = σ (SplitPosU i) := by
      simpa [SplitEdge, E, min_eq_left hl.le] using congrArg Prod.fst ht
    have hright : τ (SplitPosV (p i)) = σ (SplitPosV i) := by
      simpa [SplitEdge, E, max_eq_right hl.le] using congrArg Prod.snd ht
    fin_cases b <;> simp [f, hl, hcu, hcv, hleft, hright]
  · have hl' : σ (SplitPosV i) < σ (SplitPosU i) :=
      lt_of_le_of_ne (le_of_not_gt hl) (σ.injective.ne (hune i)).symm
    have hleft : τ (SplitPosU (p i)) = σ (SplitPosV i) := by
      simpa [SplitEdge, E, min_eq_right hl'.le] using congrArg Prod.fst ht
    have hright : τ (SplitPosV (p i)) = σ (SplitPosU i) := by
      simpa [SplitEdge, E, max_eq_left hl'.le] using congrArg Prod.snd ht
    fin_cases b <;> simp [f, hl, hcu, hcv, hleft, hright]

set_option autoImplicit false
open Common Sierksma
noncomputable section

theorem Sierksma.split_sign_algebra (π σ : Equiv.Perm (Fin 9)) :
    SplitSign (π * σ) = SplitSign π * SplitSign σ ∧
      SplitSign π * SplitSign π = 1 := by
  constructor
  · simp [SplitSign, Equiv.Perm.sign_mul, Int.cast_mul]
  · have h : (Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ) = 1 :=
      Int.isUnit_mul_self (Equiv.Perm.sign π).isUnit
    simpa only [SplitSign, Int.cast_mul, Int.cast_one] using
      congrArg (fun z : ℤ => (z : ZMod 3)) h

set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
noncomputable section

theorem Sierksma.split_reindex_orientation (σ τ : Equiv.Perm (Fin 9)) (p : Equiv.Perm (Fin 4))
    (f : Fin 4 → Equiv.Perm (Fin 2)) (h0 : σ 0 = τ 0)
    (hpos : ∀ i b, σ (SplitCoordinate (Sum.inr (i, b))) =
      τ (SplitCoordinate (Sum.inr (p i, f i b)))) (c : Fin 9 → ZMod 3) :
    SplitSign σ * (∏ i : Fin 4, (c (σ (SplitPosV i)) - c (σ (SplitPosU i)))) =
      SplitSign τ * (∏ i : Fin 4, (c (τ (SplitPosV i)) - c (τ (SplitPosU i)))) := by
  classical
  let e := SplitCoordinate
  have e0 : e (Sum.inl (0 : Fin 1)) = 0 := rfl
  have eu (i : Fin 4) : e (Sum.inr (i, (0 : Fin 2))) = SplitPosU i := by
    fin_cases i <;> rfl
  have ev (i : Fin 4) : e (Sum.inr (i, (1 : Fin 2))) = SplitPosV i := by
    fin_cases i <;> rfl
  let g : Equiv.Perm (Fin 4 × Fin 2) :=
    (Equiv.prodCongr p (Equiv.refl (Fin 2))) * Equiv.prodCongrRight f
  let ρ : Equiv.Perm (Fin 9) :=
    e.permCongr (Equiv.sumCongr (1 : Equiv.Perm (Fin 1)) g)
  have hperm : σ = τ * ρ := by
    apply Equiv.ext
    intro k
    obtain ⟨x, rfl⟩ := e.surjective k
    change σ (e x) = τ (e ((Equiv.sumCongr (1 : Equiv.Perm (Fin 1)) g) (e.symm (e x))))
    rw [e.symm_apply_apply]
    rcases x with a | ⟨i, b⟩
    · fin_cases a
      change σ 0 = τ 0
      exact h0
    · simpa [g, Equiv.Perm.mul_apply, e] using hpos i b
  have hp : Equiv.Perm.sign (Equiv.prodCongr p (Equiv.refl (Fin 2))) = 1 := by
    have heq : Equiv.prodCongr p (Equiv.refl (Fin 2)) =
        Equiv.prodCongrLeft (fun _ : Fin 2 => p) := by ext x <;> rfl
    rw [heq, Equiv.Perm.sign_prodCongrLeft, Fin.prod_univ_two]
    calc
      Equiv.Perm.sign p * Equiv.Perm.sign p =
          (Equiv.Perm.sign p)⁻¹ * Equiv.Perm.sign p := by rw [Int.units_inv_eq_self]
      _ = 1 := inv_mul_cancel _
  have hρ : Equiv.Perm.sign ρ = ∏ i, Equiv.Perm.sign (f i) := by
    simp only [ρ, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.sign_one, one_mul, g, Equiv.Perm.sign_mul, hp,
      Equiv.Perm.sign_prodCongrRight]
  let a : ZMod 3 := ∏ i, ((Equiv.Perm.sign (f i) : ℤ) : ZMod 3)
  have ha : SplitSign ρ = a := by
    simp [SplitSign, hρ, a, Int.cast_prod]
  have hs : SplitSign σ = SplitSign τ * a := by
    rw [hperm, (split_sign_algebra τ ρ).1, ha]
  have ha2 : a * a = 1 := by
    rw [← ha]
    exact (split_sign_algebra ρ ρ).2
  have hcases : ∀ q : Equiv.Perm (Fin 2), q = 1 ∨ q = Equiv.swap 0 1 := by decide
  have hd (i : Fin 4) : c (σ (SplitPosV i)) - c (σ (SplitPosU i)) =
      ((Equiv.Perm.sign (f i) : ℤ) : ZMod 3) *
        (c (τ (SplitPosV (p i))) - c (τ (SplitPosU (p i)))) := by
    rw [← ev i, ← eu i]
    change c (σ (SplitCoordinate (Sum.inr (i, (1 : Fin 2))))) -
      c (σ (SplitCoordinate (Sum.inr (i, (0 : Fin 2))))) = _
    rw [hpos, hpos]
    change c (τ (e (Sum.inr (p i, (f i) (1 : Fin 2))))) -
      c (τ (e (Sum.inr (p i, (f i) (0 : Fin 2))))) = _
    rcases hcases (f i) with h | h
    · simp [h, eu, ev]
    · simp [h, eu, ev, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  have hprod : (∏ i : Fin 4, (c (σ (SplitPosV i)) - c (σ (SplitPosU i)))) =
      a * ∏ i : Fin 4, (c (τ (SplitPosV i)) - c (τ (SplitPosU i))) := by
    simp_rw [hd]
    rw [Finset.prod_mul_distrib]
    change a * (∏ i, (c (τ (SplitPosV (p i))) - c (τ (SplitPosU (p i))))) = _
    exact congrArg (fun z : ZMod 3 => a * z)
      (Equiv.prod_comp p (fun i : Fin 4 => c (τ (SplitPosV i)) - c (τ (SplitPosU i))))
  rw [hs, hprod]
  calc
    SplitSign τ * a * (a * ∏ i : Fin 4, (c (τ (SplitPosV i)) - c (τ (SplitPosU i)))) =
        SplitSign τ * (a * a) * ∏ i : Fin 4, (c (τ (SplitPosV i)) - c (τ (SplitPosU i))) := by ring
    _ = _ := by rw [ha2, mul_one]

set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
noncomputable section

theorem Sierksma.signed_system_all_splittings (y : Common.Partition 9 → ZMod 3) (hy : SignedSystem y)
    (σ : Equiv.Perm (Fin 9)) :
    ∑ Q ∈ ThreePartitions 9, y Q * SplitSign σ *
      (∏ i : Fin 4, EdgeDiff Q (SplitEdge σ i)) = 2 := by
  classical
  obtain ⟨τ, hτ, p, f, h0, hpos⟩ := split_normalization σ
  calc
    _ = ∑ Q ∈ ThreePartitions 9, y Q * SplitSign τ *
        (∏ i : Fin 4, EdgeDiff Q (SplitEdge τ i)) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have ht := split_reindex_orientation σ τ p f h0 hpos (CanonColour Q)
      change SplitSign σ * (∏ i : Fin 4, EdgeDiff Q (SplitEdge σ i)) =
        SplitSign τ * (∏ i : Fin 4, EdgeDiff Q (SplitEdge τ i)) at ht
      simpa only [mul_assoc] using congrArg (fun z : ZMod 3 => y Q * z) ht
    _ = 2 := hy.2.2 τ hτ

set_option autoImplicit false
open Common Sierksma
noncomputable section

theorem Sierksma.signed_relabel_support (y : Common.Partition 9 → ZMod 3) (π : Equiv.Perm (Fin 9)) :
    (Finset.univ.filter (fun Q : Common.Partition 9 =>
      SplitSign π * y (Relabel π.symm Q) ≠ 0)) =
    RelabelFamily π (Finset.univ.filter (fun Q : Common.Partition 9 => y Q ≠ 0)) := by
  classical
  have hs : SplitSign π ≠ 0 := by
    intro h
    have hsq := (split_sign_algebra π π).2
    simp [h] at hsq
  ext Q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, RelabelFamily,
    Finset.mem_image, mul_ne_zero_iff]
  constructor
  · intro h
    refine ⟨Relabel π.symm Q, h.2, ?_⟩
    simpa using (partition_relabel_inverse_type π.symm Q).1
  · rintro ⟨R, hR, rfl⟩
    exact ⟨hs, by simpa only [(partition_relabel_inverse_type π R).1] using hR⟩

open scoped BigOperators
open Common Sierksma
noncomputable section

theorem proof_Sierksma_signed_relabel (y : Common.Partition 9 → ZMod 3)
    (hy : SignedSystem y) (π : Equiv.Perm (Fin 9)) :
    SignedSystem (fun Q => SplitSign π * y (Relabel π.symm Q)) ∧
      (Finset.univ.filter (fun Q : Common.Partition 9 =>
        SplitSign π * y (Relabel π.symm Q) ≠ 0)) =
        RelabelFamily π (Finset.univ.filter (fun Q : Common.Partition 9 => y Q ≠ 0)) := by
  classical
  let r : Equiv.Perm (Common.Partition 9) :=
    { toFun := Relabel π
      invFun := Relabel π.symm
      left_inv := fun Q => (partition_relabel_inverse_type π Q).1
      right_inv := fun Q => by simpa using (partition_relabel_inverse_type π.symm Q).1 }
  have hmem (Q : Common.Partition 9) :
      Relabel π Q ∈ ThreePartitions 9 ↔ Q ∈ ThreePartitions 9 := by
    simp only [ThreePartitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact is_partition_relabel π Q
  have reindex (F : Common.Partition 9 → ZMod 3) :
      (∑ Q ∈ ThreePartitions 9, F Q) = ∑ Q ∈ ThreePartitions 9, F (Relabel π Q) := by
    symm
    apply Finset.sum_equiv r
    · intro Q
      exact (hmem Q).symm
    · intro Q hQ
      rfl
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · calc
        _ = ∑ Q ∈ ThreePartitions 9, SplitSign π * y Q := by
          rw [reindex (fun Q => SplitSign π * y (Relabel π.symm Q))]
          apply Finset.sum_congr rfl
          intro Q hQ
          rw [(partition_relabel_inverse_type π Q).1]
        _ = SplitSign π * ∑ Q ∈ ThreePartitions 9, y Q := by rw [Finset.mul_sum]
        _ = 0 := by rw [hy.1, mul_zero]
    · intro e f he hf hdis
      let e' : Edge 9 := (π.symm e.1, π.symm e.2)
      let f' : Edge 9 := (π.symm f.1, π.symm f.2)
      have hdis' : Disjoint (Endpoints e') (Endpoints f') := by
        simpa [Endpoints, e', f'] using (Finset.disjoint_image π.symm.injective).mpr hdis
      have h2 (Q : Common.Partition 9) (hQ : Q ∈ ThreePartitions 9) :
          EdgeDiff (Relabel π Q) e * EdgeDiff (Relabel π Q) f =
            EdgeDiff Q e' * EdgeDiff Q f' := by
        have hQpart : IsPartition Q 3 := (Finset.mem_filter.mp hQ).2
        simpa [e', f'] using (edge_diff_relabel_even π Q hQpart).1 e' f'
      calc
        _ = ∑ Q ∈ ThreePartitions 9, SplitSign π * y Q * EdgeDiff Q e' * EdgeDiff Q f' := by
          rw [reindex (fun Q => SplitSign π * y (Relabel π.symm Q) * EdgeDiff Q e * EdgeDiff Q f)]
          apply Finset.sum_congr rfl
          intro Q hQ
          rw [(partition_relabel_inverse_type π Q).1]
          simp only [mul_assoc]
          rw [h2 Q hQ]
        _ = SplitSign π * ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q e' * EdgeDiff Q f' := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro Q hQ
          ring
        _ = 0 := by rw [signed_system_unordered_pairs y hy e' f' hdis', mul_zero]
    · intro σ hσ
      let θ : Equiv.Perm (Fin 9) := π.symm * σ
      have hsign : SplitSign π * SplitSign σ = SplitSign θ := by
        simp [θ, SplitSign, Equiv.Perm.sign_mul, Int.cast_mul]
      have h4 (Q : Common.Partition 9) (hQ : Q ∈ ThreePartitions 9) :
          (∏ i : Fin 4, EdgeDiff (Relabel π Q) (SplitEdge σ i)) =
            ∏ i : Fin 4, EdgeDiff Q (SplitEdge θ i) := by
        have hQpart : IsPartition Q 3 := (Finset.mem_filter.mp hQ).2
        have h := (edge_diff_relabel_even π Q hQpart).2 (fun i => SplitEdge θ i)
        simpa [θ, SplitEdge, Equiv.Perm.mul_apply] using h
      calc
        _ = ∑ Q ∈ ThreePartitions 9, y Q * SplitSign θ *
            (∏ i : Fin 4, EdgeDiff Q (SplitEdge θ i)) := by
          rw [reindex (fun Q => SplitSign π * y (Relabel π.symm Q) * SplitSign σ *
            (∏ i : Fin 4, EdgeDiff Q (SplitEdge σ i)))]
          apply Finset.sum_congr rfl
          intro Q hQ
          rw [(partition_relabel_inverse_type π Q).1, h4 Q hQ]
          calc
            _ = y Q * (SplitSign π * SplitSign σ) *
                (∏ i : Fin 4, EdgeDiff Q (SplitEdge θ i)) := by ring
            _ = _ := by rw [hsign]
        _ = 2 := signed_system_all_splittings y hy θ
  · exact signed_relabel_support y π
