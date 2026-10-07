import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
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

theorem proof_Sierksma_canon_colour_respects {n : ℕ}
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
