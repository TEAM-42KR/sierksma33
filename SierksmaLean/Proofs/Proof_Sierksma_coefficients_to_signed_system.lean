import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem teMultiaffine
    (a : Finset (Fin 4) → ZMod 3) (k : ZMod 3)
    (h : ∀ c : Fin 4 → ZMod 3, MultiaffineEval a c = k) :
    a ∅ = k ∧ ∀ s : Finset (Fin 4), s ≠ ∅ → a s = 0 := by
  classical
  have heval (s : Finset (Fin 4)) : ∑ t ∈ s.powerset, a t = k := by
    have hh := h (fun i => if i ∈ s then 1 else 0)
    unfold MultiaffineEval at hh
    have hp (t : Finset (Fin 4)) :
        (∏ i ∈ t, (if i ∈ s then (1 : ZMod 3) else 0)) = if t ⊆ s then 1 else 0 := by
      by_cases ht : t ⊆ s
      · simp [ht, Finset.prod_eq_one (fun i hi => if_pos (ht hi))]
      · obtain ⟨i, hi, his⟩ := Finset.not_subset.mp ht
        rw [if_neg ht]
        exact Finset.prod_eq_zero hi (if_neg his)
    simp_rw [hp, mul_ite, mul_one, mul_zero] at hh
    rw [← Finset.sum_filter] at hh
    have hset : (Finset.univ.filter (fun t : Finset (Fin 4) => t ⊆ s)) = s.powerset := by
      ext t
      simp
    rwa [hset] at hh
  have hempty : a ∅ = k := by simpa using heval ∅
  refine ⟨hempty, ?_⟩
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro hs
    have hh := heval s
    have hsum : ∑ t ∈ s.powerset, a t = a s + a ∅ := by
      rw [← Finset.add_sum_erase s.powerset a (Finset.mem_powerset_self s)]
      congr 1
      apply Finset.sum_eq_single ∅
      · intro t ht ht0
        exact ih t (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2,
          (Finset.mem_erase.mp ht).1⟩) ht0
      · intro ht
        exact False.elim (ht (Finset.mem_erase.mpr ⟨Ne.symm hs, Finset.empty_mem_powerset s⟩))
    rw [hsum, hempty] at hh
    have hc : a s + k = 0 + k := by simpa using hh
    exact add_right_cancel hc

private theorem teMoments
    (y : Common.Partition 9 → ZMod 3) (pi : Equiv.Perm (Fin 9))
    (h : ∀ c : Fin 4 → ZMod 3, TwistPolynomial y pi c = 1) :
    (∑ Q ∈ ThreePartitions 9, y Q = 0) ∧
    (∀ i j : Fin 4, i ≠ j →
      ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi i) * EdgeDiff Q (SplitEdge pi j) = 0) ∧
    (∑ Q ∈ ThreePartitions 9, y Q * SplitSign pi * ∏ i : Fin 4, EdgeDiff Q (SplitEdge pi i) = 2) := by
  classical
  have hprod (d c : Fin 4 → ZMod 3) :
      (∏ i, (d i - c i)) + (∏ i, (-d i - c i)) =
      2 * (d 0*d 1*d 2*d 3 + c 0*c 1*d 2*d 3 + c 0*c 2*d 1*d 3 + c 0*c 3*d 1*d 2 + c 1*c 2*d 0*d 3 + c 1*c 3*d 0*d 2 + c 2*c 3*d 0*d 1 + c 0*c 1*c 2*c 3) := by
    simp only [Fin.prod_univ_four]
    ring
  let a : Finset (Fin 4) → ZMod 3 := fun s =>
    (if s = ∅ then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * ∏ i : Fin 4, EdgeDiff Q (SplitEdge pi i)) else 0) +
    (if s = {2,3} then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 0) * EdgeDiff Q (SplitEdge pi 1)) else 0) +
    (if s = {1,3} then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 0) * EdgeDiff Q (SplitEdge pi 2)) else 0) +
    (if s = {1,2} then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 0) * EdgeDiff Q (SplitEdge pi 3)) else 0) +
    (if s = {0,3} then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 1) * EdgeDiff Q (SplitEdge pi 2)) else 0) +
    (if s = {0,2} then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 1) * EdgeDiff Q (SplitEdge pi 3)) else 0) +
    (if s = {0,1} then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 2) * EdgeDiff Q (SplitEdge pi 3)) else 0) +
    (if s = {0,1,2,3} then 2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q) else 0)
  have ha : ∀ c, MultiaffineEval a c = 1 := by
    intro c
    have hh := h c
    unfold TwistPolynomial at hh
    rw [← hh]
    simp_rw [hprod]
    simp [MultiaffineEval, a, add_mul, ite_mul, Finset.sum_add_distrib, Fin.prod_univ_four]
    simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    simp only [mul_assoc, mul_comm, mul_left_comm]
    ring
  have hc := teMultiaffine a 1 ha
  have hs : SplitSign pi * SplitSign pi = 1 := by
    unfold SplitSign
    norm_cast
    simp [Int.units_mul_self]
  have hn : 2 * SplitSign pi ≠ 0 := by
    apply mul_ne_zero (by decide)
    intro hz
    simp [hz] at hs
  have hz (s : Finset (Fin 4)) (hne : s ≠ ∅) : a s = 0 := hc.2 s hne
  have h0 := hz {0,1,2,3} (by decide)
  simp only [a, show ({0,1,2,3} : Finset (Fin 4)) ≠ ∅ from by decide, show ({0,1,2,3} : Finset (Fin 4)) ≠ {2,3} from by decide, show ({0,1,2,3} : Finset (Fin 4)) ≠ {1,3} from by decide, show ({0,1,2,3} : Finset (Fin 4)) ≠ {1,2} from by decide, show ({0,1,2,3} : Finset (Fin 4)) ≠ {0,3} from by decide, show ({0,1,2,3} : Finset (Fin 4)) ≠ {0,2} from by decide, show ({0,1,2,3} : Finset (Fin 4)) ≠ {0,1} from by decide, if_false, if_true, zero_add, add_zero] at h0
  have hzero : ∑ Q ∈ ThreePartitions 9, y Q = 0 := (mul_eq_zero.mp h0).resolve_left hn
  have h01 : ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 0) * EdgeDiff Q (SplitEdge pi 1) = 0 := by
    have hx := hz {2,3} (by decide)
    simp only [a, show ({2,3} : Finset (Fin 4)) ≠ ∅ from by decide, show ({2,3} : Finset (Fin 4)) ≠ {1,3} from by decide, show ({2,3} : Finset (Fin 4)) ≠ {1,2} from by decide, show ({2,3} : Finset (Fin 4)) ≠ {0,3} from by decide, show ({2,3} : Finset (Fin 4)) ≠ {0,2} from by decide, show ({2,3} : Finset (Fin 4)) ≠ {0,1} from by decide, show ({2,3} : Finset (Fin 4)) ≠ {0,1,2,3} from by decide, if_false, if_true, zero_add, add_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left hn
  have h02 : ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 0) * EdgeDiff Q (SplitEdge pi 2) = 0 := by
    have hx := hz {1,3} (by decide)
    simp only [a, show ({1,3} : Finset (Fin 4)) ≠ ∅ from by decide, show ({1,3} : Finset (Fin 4)) ≠ {2,3} from by decide, show ({1,3} : Finset (Fin 4)) ≠ {1,2} from by decide, show ({1,3} : Finset (Fin 4)) ≠ {0,3} from by decide, show ({1,3} : Finset (Fin 4)) ≠ {0,2} from by decide, show ({1,3} : Finset (Fin 4)) ≠ {0,1} from by decide, show ({1,3} : Finset (Fin 4)) ≠ {0,1,2,3} from by decide, if_false, if_true, zero_add, add_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left hn
  have h03 : ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 0) * EdgeDiff Q (SplitEdge pi 3) = 0 := by
    have hx := hz {1,2} (by decide)
    simp only [a, show ({1,2} : Finset (Fin 4)) ≠ ∅ from by decide, show ({1,2} : Finset (Fin 4)) ≠ {2,3} from by decide, show ({1,2} : Finset (Fin 4)) ≠ {1,3} from by decide, show ({1,2} : Finset (Fin 4)) ≠ {0,3} from by decide, show ({1,2} : Finset (Fin 4)) ≠ {0,2} from by decide, show ({1,2} : Finset (Fin 4)) ≠ {0,1} from by decide, show ({1,2} : Finset (Fin 4)) ≠ {0,1,2,3} from by decide, if_false, if_true, zero_add, add_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left hn
  have h12 : ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 1) * EdgeDiff Q (SplitEdge pi 2) = 0 := by
    have hx := hz {0,3} (by decide)
    simp only [a, show ({0,3} : Finset (Fin 4)) ≠ ∅ from by decide, show ({0,3} : Finset (Fin 4)) ≠ {2,3} from by decide, show ({0,3} : Finset (Fin 4)) ≠ {1,3} from by decide, show ({0,3} : Finset (Fin 4)) ≠ {1,2} from by decide, show ({0,3} : Finset (Fin 4)) ≠ {0,2} from by decide, show ({0,3} : Finset (Fin 4)) ≠ {0,1} from by decide, show ({0,3} : Finset (Fin 4)) ≠ {0,1,2,3} from by decide, if_false, if_true, zero_add, add_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left hn
  have h13 : ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 1) * EdgeDiff Q (SplitEdge pi 3) = 0 := by
    have hx := hz {0,2} (by decide)
    simp only [a, show ({0,2} : Finset (Fin 4)) ≠ ∅ from by decide, show ({0,2} : Finset (Fin 4)) ≠ {2,3} from by decide, show ({0,2} : Finset (Fin 4)) ≠ {1,3} from by decide, show ({0,2} : Finset (Fin 4)) ≠ {1,2} from by decide, show ({0,2} : Finset (Fin 4)) ≠ {0,3} from by decide, show ({0,2} : Finset (Fin 4)) ≠ {0,1} from by decide, show ({0,2} : Finset (Fin 4)) ≠ {0,1,2,3} from by decide, if_false, if_true, zero_add, add_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left hn
  have h23 : ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi 2) * EdgeDiff Q (SplitEdge pi 3) = 0 := by
    have hx := hz {0,1} (by decide)
    simp only [a, show ({0,1} : Finset (Fin 4)) ≠ ∅ from by decide, show ({0,1} : Finset (Fin 4)) ≠ {2,3} from by decide, show ({0,1} : Finset (Fin 4)) ≠ {1,3} from by decide, show ({0,1} : Finset (Fin 4)) ≠ {1,2} from by decide, show ({0,1} : Finset (Fin 4)) ≠ {0,3} from by decide, show ({0,1} : Finset (Fin 4)) ≠ {0,2} from by decide, show ({0,1} : Finset (Fin 4)) ≠ {0,1,2,3} from by decide, if_false, if_true, zero_add, add_zero] at hx
    exact (mul_eq_zero.mp hx).resolve_left hn
  have hfull : (∑ Q ∈ ThreePartitions 9, y Q * SplitSign pi * ∏ i : Fin 4, EdgeDiff Q (SplitEdge pi i)) = 2 := by
    have hx := hc.1
    simp only [a, show (∅ : Finset (Fin 4)) ≠ {2,3} from by decide, show (∅ : Finset (Fin 4)) ≠ {1,3} from by decide, show (∅ : Finset (Fin 4)) ≠ {1,2} from by decide, show (∅ : Finset (Fin 4)) ≠ {0,3} from by decide, show (∅ : Finset (Fin 4)) ≠ {0,2} from by decide, show (∅ : Finset (Fin 4)) ≠ {0,1} from by decide, show (∅ : Finset (Fin 4)) ≠ {0,1,2,3} from by decide, if_false, if_true, zero_add, add_zero] at hx
    apply mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0)
    calc
      2 * (∑ Q ∈ ThreePartitions 9, y Q * SplitSign pi * ∏ i, EdgeDiff Q (SplitEdge pi i)) =
          2 * SplitSign pi * (∑ Q ∈ ThreePartitions 9, y Q * ∏ i, EdgeDiff Q (SplitEdge pi i)) := by
            simp only [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := hx
      _ = 2 * 2 := by decide
  have hsym (i j : Fin 4) :
      (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi i) * EdgeDiff Q (SplitEdge pi j)) =
      (∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (SplitEdge pi j) * EdgeDiff Q (SplitEdge pi i)) := by
    apply Finset.sum_congr rfl
    intro Q hQ
    ring
  refine ⟨hzero, ?_, hfull⟩
  clear h hprod a ha hc hs hn hz h0 hzero hfull
  intro i j hij
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  · exact h01
  · exact h02
  · exact h03
  · exact (hsym 1 0).trans h01
  · exact h12
  · exact h13
  · exact (hsym 2 0).trans h02
  · exact (hsym 2 1).trans h12
  · exact h23
  · exact (hsym 3 0).trans h03
  · exact (hsym 3 1).trans h13
  · exact (hsym 3 2).trans h23

private theorem teSplittingOfMatching (M : Finset (Edge 9)) (hM : IsMatching M) (hc : M.card = 4) :
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

private theorem tePairExtension (e f : Edge 9)
    (he : e.1 < e.2) (hf : f.1 < f.2) (hd : Disjoint (Endpoints e) (Endpoints f)) :
    ∃ pi : Equiv.Perm (Fin 9), IsSplitting pi ∧
      ∃ i j : Fin 4, i ≠ j ∧ SplitEdge pi i = e ∧ SplitEdge pi j = f := by
  classical
  let R : Finset (Fin 9) := Finset.univ \ (Endpoints e ∪ Endpoints f)
  have hce : (Endpoints e).card = 2 := by simp [Endpoints, ne_of_lt he]
  have hcf : (Endpoints f).card = 2 := by simp [Endpoints, ne_of_lt hf]
  have hR : R.card = 5 := by
    simp only [R, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hd, hce, hcf, Finset.card_univ, Fintype.card_fin]
  let g : Fin 5 ↪o Fin 9 := R.orderEmbOfFin hR
  have hge (i : Fin 5) : g i ∉ Endpoints e := by
    have h := Finset.mem_sdiff.mp (Finset.orderEmbOfFin_mem R hR i)
    exact fun hi => h.2 (Finset.mem_union_left _ hi)
  have hgf (i : Fin 5) : g i ∉ Endpoints f := by
    have h := Finset.mem_sdiff.mp (Finset.orderEmbOfFin_mem R hR i)
    exact fun hi => h.2 (Finset.mem_union_right _ hi)
  let a : Edge 9 := (g 0, g 1)
  let b : Edge 9 := (g 2, g 3)
  have ha : a.1 < a.2 := g.strictMono (by decide)
  have hb : b.1 < b.2 := g.strictMono (by decide)
  have hne (i j : Fin 5) (hij : i ≠ j) : g i ≠ g j := fun h => hij (g.injective h)
  have hae : Disjoint (Endpoints a) (Endpoints e) := by
    change Disjoint {g 0, g 1} (Endpoints e)
    rw [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hge 0, hge 1⟩
  have haf : Disjoint (Endpoints a) (Endpoints f) := by
    change Disjoint {g 0, g 1} (Endpoints f)
    rw [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hgf 0, hgf 1⟩
  have hbe : Disjoint (Endpoints b) (Endpoints e) := by
    change Disjoint {g 2, g 3} (Endpoints e)
    rw [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hge 2, hge 3⟩
  have hbf : Disjoint (Endpoints b) (Endpoints f) := by
    change Disjoint {g 2, g 3} (Endpoints f)
    rw [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hgf 2, hgf 3⟩
  have habd : Disjoint (Endpoints a) (Endpoints b) := by
    simp only [Endpoints, a, b, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨⟨hne 0 2 (by decide), hne 0 3 (by decide)⟩,
      ⟨hne 1 2 (by decide), hne 1 3 (by decide)⟩⟩
  have hneq (x z : Edge 9) (hxz : Disjoint (Endpoints x) (Endpoints z)) : x ≠ z := by
    intro h
    have hm : x.1 ∈ Endpoints x := by simp [Endpoints]
    exact Finset.disjoint_left.mp hxz hm (by simpa [h] using hm)
  have hef := hneq e f hd
  have hea := hneq e a hae.symm
  have heb := hneq e b hbe.symm
  have hfa := hneq f a haf.symm
  have hfb := hneq f b hbf.symm
  have hab := hneq a b habd
  let M : Finset (Edge 9) := {e,f,a,b}
  have hm : IsMatching M := by
    simp only [IsMatching, M, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨⟨he, hf, ha, hb⟩, by
      simp [hd, hae, haf, hbe, hbf, habd, hae.symm, haf.symm, hbe.symm, hbf.symm, habd.symm, hd.symm]⟩
  have hc : M.card = 4 := by
    simp [M, hef, hea, heb, hfa, hfb, hab]
  obtain ⟨pi, hpi, henum⟩ := teSplittingOfMatching M hm hc
  obtain ⟨i, hi⟩ := (henum e).mp (by simp [M])
  obtain ⟨j, hj⟩ := (henum f).mp (by simp [M])
  refine ⟨pi, hpi, i, j, ?_, hi, hj⟩
  intro hij
  exact hef (hi.symm.trans (hij ▸ hj))

theorem proof_Sierksma_coefficients_to_signed_system
    (y : Common.Partition 9 → ZMod 3)
    (h : ∀ pi : Equiv.Perm (Fin 9), IsSplitting pi → ∀ c : Fin 4 → ZMod 3, TwistPolynomial y pi c = 1) :
    SignedSystem y := by
  have hid : IsSplitting (1 : Equiv.Perm (Fin 9)) := by decide
  have hzero := (teMoments y 1 (h 1 hid)).1
  refine ⟨hzero, ?_, ?_⟩
  · intro e f he hf hd
    obtain ⟨pi, hpi, i, j, hij, hi, hj⟩ := tePairExtension e f he hf hd
    have hp := (teMoments y pi (h pi hpi)).2.1 i j hij
    simpa only [hi, hj] using hp
  · intro pi hpi
    exact (teMoments y pi (h pi hpi)).2.2
