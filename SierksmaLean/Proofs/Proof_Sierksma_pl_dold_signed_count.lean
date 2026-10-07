import SierksmaLean.Theorems.Thm_PLDegree_apex_independence
import SierksmaLean.Theorems.Thm_Sierksma_hexagon_join_cycle
import SierksmaLean.Theorems.Thm_Sierksma_pl_orbit_move_multiple_three
import SierksmaLean.Theorems.Thm_Sierksma_pl_equivariant_gp_dense
import SierksmaLean.Theorems.Thm_Sierksma_pl_model_count_one
import SierksmaLean.Theorems.Thm_PLDegree_finite_hull_zero_closed
import SierksmaLean.Theorems.Thm_PLDegree_simplex_degree_nonzero_mem_hull
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem proof_Sierksma_pl_dold_signed_count :
    (∀ x : EngineParams, EngineGeneric x →
      (∀ j k : Fin 3, ConeCount x j=ConeCount x k) ∧
      ∀ j : Fin 3, ConeCount x j % 3=1) ∧
    (∀ x : EngineParams, ∃ j : Fin 3, ∃ s ∈ (EngineCone j).support,
      (0 : W8) ∈ PLDegree.hull (EngineMap x) s) := by
  classical
  obtain ⟨hh, hcycle, hshift, hsupport⟩ := Sierksma.hexagon_join_cycle
  obtain ⟨hdense, hopen, hpath⟩ := Sierksma.pl_equivariant_gp_dense
  obtain ⟨hcheck, hmodel, hcount⟩ := Sierksma.pl_model_count_one
  have hfresh : ∀ j : Fin 3, Fresh (24+j.val) HexCycle := by
    intro j s hs hmem
    have hlt := (hsupport s hs (24+j.val) hmem).1
    omega
  have hgeneric : ∀ x : EngineParams, EngineGeneric x →
      (∀ j k : Fin 3, ConeCount x j=ConeCount x k) ∧
      ∀ j : Fin 3, ConeCount x j % 3=1 := by
    intro x hx
    constructor
    · intro j k
      exact PLDegree.apex_independence (by decide) (EngineMap x) HexCycle
        (24+j.val) (24+k.val) hh hcycle (hfresh j) (hfresh k) (hx j) (hx k)
    · intro j
      obtain ⟨m, p, hp0, hplast, hgp, hmove⟩ := hpath x ModelParams hx hmodel
      have hp : ∀ i : Fin (m+1), ConeCount (p i) j % 3=ConeCount x j % 3 := by
        intro i
        induction i using Fin.induction with
        | zero => rw [hp0]
        | succ i ih =>
          have hd := Sierksma.pl_orbit_move_multiple_three
            (p i.castSucc) (p i.succ) (hgp _) (hgp _) (hmove i) j
          have he : ConeCount (p i.castSucc) j % 3 = ConeCount (p i.succ) j % 3 := by
            rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
            exact Int.dvd_iff_emod_eq_zero.mp hd
          exact he.symm.trans ih
      have he := hp (Fin.last m)
      rw [hplast, hcount j] at he
      norm_num at he
      exact he.symm
  refine ⟨hgeneric, ?_⟩
  have hR : Continuous R8 := by
    apply continuous_pi
    intro j
    unfold R8
    split_ifs <;> fun_prop
  have hmap : Continuous (fun x : EngineParams => EngineMap x) := by
    apply continuous_pi
    intro v
    unfold EngineMap RPower
    split_ifs
    · exact (hR.iterate _).comp (continuous_apply _)
    · exact (hR.iterate _).comp (continuous_apply _)
    · exact continuous_const
  let Z : Set EngineParams := {x | ∃ j : Fin 3, ∃ s ∈ (EngineCone j).support,
    (0 : W8) ∈ PLDegree.hull (EngineMap x) s}
  have hZ : IsClosed Z := by
    have heq : Z = ⋃ j : Fin 3, ⋃ s ∈ (EngineCone j).support,
        {x : EngineParams | (0 : W8) ∈ PLDegree.hull (EngineMap x) s} := by
      ext x
      simp [Z]
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro j
    apply isClosed_biUnion_finset
    intro s hs
    exact (PLDegree.finite_hull_zero_closed s).preimage hmap
  have hgZ : {x : EngineParams | EngineGeneric x} ⊆ Z := by
    intro x hx
    by_contra hn
    have hno : ∀ s ∈ (EngineCone (0 : Fin 3)).support,
        (0 : W8) ∉ PLDegree.hull (EngineMap x) s := by
      intro s hs hhull
      exact hn ⟨0,s,hs,hhull⟩
    have hzero : ConeCount x (0 : Fin 3)=0 := by
      unfold ConeCount signedCount evaluate Finsupp.sum
      apply Finset.sum_eq_zero
      intro s hs
      have hsd : simplexDegree (EngineMap x) s=0 := by
        by_contra h
        exact hno s hs (PLDegree.simplex_degree_nonzero_mem_hull _ _ h)
      simp [hsd]
    have hmod := (hgeneric x hx).2 (0 : Fin 3)
    rw [hzero] at hmod
    norm_num at hmod
  have hc := closure_mono hgZ
  rw [hdense.closure_eq, hZ.closure_eq] at hc
  intro x
  exact hc (Set.mem_univ x)
