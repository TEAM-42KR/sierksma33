import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
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

theorem Sierksma.signed_twist_sum (y : Common.Partition 9 → ZMod 3)
    (hy : SignedSystem y) (σ : Equiv.Perm (Fin 9)) (hσ : IsSplitting σ)
    (c : Fin 4 → ZMod 3) :
    (∑ Q ∈ ThreePartitions 9, y Q * SplitSign σ *
      ((∏ i : Fin 4, (EdgeDiff Q (SplitEdge σ i) - c i)) +
        ∏ i : Fin 4, (-EdgeDiff Q (SplitEdge σ i) - c i))) = 1 := by
  classical
  let d (Q : Common.Partition 9) (i : Fin 4) := EdgeDiff Q (SplitEdge σ i)
  have hp (i j : Fin 4) (hij : i ≠ j) :
      ∑ Q ∈ ThreePartitions 9, y Q * d Q i * d Q j = 0 :=
    hy.2.1 (SplitEdge σ i) (SplitEdge σ j) (hσ.1 i) (hσ.1 j)
      (Sierksma.split_edges_pairwise_disjoint σ i j hij)
  have hfull : ∑ Q ∈ ThreePartitions 9,
      y Q * SplitSign σ * (d Q 0 * d Q 1 * d Q 2 * d Q 3) = 2 := by
    simpa only [Fin.prod_univ_four] using hy.2.2 σ hσ
  have hexpand : (∑ Q ∈ ThreePartitions 9, y Q * SplitSign σ *
      ((∏ i : Fin 4, (d Q i - c i)) +
        ∏ i : Fin 4, (-d Q i - c i))) =
      2 * (∑ Q ∈ ThreePartitions 9, y Q * SplitSign σ *
        (d Q 0 * d Q 1 * d Q 2 * d Q 3)) +
      (2 * SplitSign σ * c 0 * c 1 * c 2 * c 3) *
        (∑ Q ∈ ThreePartitions 9, y Q) +
      (2 * SplitSign σ * c 2 * c 3) *
        (∑ Q ∈ ThreePartitions 9, y Q * d Q 0 * d Q 1) +
      (2 * SplitSign σ * c 1 * c 3) *
        (∑ Q ∈ ThreePartitions 9, y Q * d Q 0 * d Q 2) +
      (2 * SplitSign σ * c 1 * c 2) *
        (∑ Q ∈ ThreePartitions 9, y Q * d Q 0 * d Q 3) +
      (2 * SplitSign σ * c 0 * c 3) *
        (∑ Q ∈ ThreePartitions 9, y Q * d Q 1 * d Q 2) +
      (2 * SplitSign σ * c 0 * c 2) *
        (∑ Q ∈ ThreePartitions 9, y Q * d Q 1 * d Q 3) +
      (2 * SplitSign σ * c 0 * c 1) *
        (∑ Q ∈ ThreePartitions 9, y Q * d Q 2 * d Q 3) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Q hQ
    simp only [Fin.prod_univ_four]
    ring
  change (∑ Q ∈ ThreePartitions 9, y Q * SplitSign σ *
    ((∏ i : Fin 4, (d Q i - c i)) + ∏ i : Fin 4, (-d Q i - c i))) = 1
  rw [hexpand, hfull, hy.1, hp 0 1 (by decide), hp 0 2 (by decide),
    hp 0 3 (by decide), hp 1 2 (by decide), hp 1 3 (by decide), hp 2 3 (by decide)]
  norm_num
  decide

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
open scoped BigOperators
open Common Sierksma
set_option autoImplicit false

theorem proof_Sierksma_signed_covers (y : Common.Partition 9 → ZMod 3)
    (hy : SignedSystem y) (g : PairConstraint 9) (hg : ValidConstraint 3 g) :
    ∃ Q ∈ ThreePartitions 9, y Q ≠ 0 ∧ Covers Q g := by
  classical
  obtain ⟨σ, hσ, hedge⟩ := Sierksma.splitting_of_matching g.matching hg.1
    (by simpa using hg.2.1)
  let c : Fin 4 → ZMod 3 := fun i => g.twists (SplitEdge σ i)
  let A : Common.Partition 9 → ZMod 3 := fun Q =>
    ∏ i : Fin 4, (EdgeDiff Q (SplitEdge σ i) - c i)
  let B : Common.Partition 9 → ZMod 3 := fun Q =>
    ∏ i : Fin 4, (-EdgeDiff Q (SplitEdge σ i) - c i)
  have hsum : (∑ Q ∈ ThreePartitions 9, y Q * SplitSign σ * (A Q + B Q)) = 1 :=
    Sierksma.signed_twist_sum y hy σ hσ c
  have hex : ∃ Q ∈ ThreePartitions 9, y Q * SplitSign σ * (A Q + B Q) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (∑ Q ∈ ThreePartitions 9, y Q * SplitSign σ * (A Q + B Q)) = 0 :=
      Finset.sum_eq_zero h
    rw [hsum] at hz
    exact one_ne_zero hz
  obtain ⟨Q, hQ, hterm⟩ := hex
  have hyQ : y Q ≠ 0 := by
    intro h
    apply hterm
    simp [h]
  have hab : A Q + B Q ≠ 0 := by
    intro h
    apply hterm
    rw [h, mul_zero]
  have hpart : IsPartition Q 3 := (Finset.mem_filter.mp hQ).2
  have hcol : Respects Q (CanonColour Q) := Sierksma.canon_colour_respects Q hpart
  refine ⟨Q, hQ, hyQ, ?_⟩
  by_cases hA : A Q ≠ 0
  · refine ⟨CanonColour Q, hcol, ?_⟩
    intro e he
    obtain ⟨i, rfl⟩ := (hedge e).mp he
    exact sub_ne_zero.mp ((Finset.prod_ne_zero_iff.mp hA) i (Finset.mem_univ i))
  · have hB : B Q ≠ 0 := by
      intro hB
      exact hab (by rw [not_not.mp hA, hB, add_zero])
    refine ⟨(fun v => -CanonColour Q v), ?_, ?_⟩
    · intro u v
      simpa only [neg_inj] using hcol u v
    · intro e he
      obtain ⟨i, rfl⟩ := (hedge e).mp he
      have hi := sub_ne_zero.mp ((Finset.prod_ne_zero_iff.mp hB) i (Finset.mem_univ i))
      simpa only [EdgeDiff, neg_sub, neg_sub_neg, c] using hi
