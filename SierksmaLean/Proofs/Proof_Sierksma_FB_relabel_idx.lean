import SierksmaLean.Theorems.Thm_Sierksma_FB_partOf_bij
import SierksmaLean.Theorems.Thm_Sierksma_FB_relIdx_spec
import SierksmaLean.Theorems.Thm_Sierksma_signed_relabel
import SierksmaLean.Theorems.Thm_Sierksma_relabel_universe
import SierksmaLean.Theorems.Thm_Sierksma_partition_relabel_inverse_type
set_option autoImplicit false
open Common Sierksma Sierksma.FB
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem proof_Sierksma_FB_relabel_idx (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Sierksma.Universe 3) (hy : Sierksma.SignedSystem y)
    (p : ℕ) (hp : Sierksma.FB.validPerm p = true) :
    ∃ y' : Common.Partition 9 → ZMod 3, Sierksma.SignedSystem y' ∧
      (∀ Q, y' Q ≠ 0 → Q ∈ Sierksma.Universe 3) ∧
      Sierksma.FB.idxSupp y' = (Sierksma.FB.idxSupp y).image (Sierksma.FB.relIdx p) := by
  classical
  have hp0 : (List.range 9).all (fun v => Nat.blt (pAt p v) 9) = true :=
    (Bool.and_eq_true_iff.mp hp).1
  have hp1 : (List.range 9).all (fun v => (List.range 9).all
      (fun w => Nat.beq v w || !(Nat.beq (pAt p v) (pAt p w)))) = true :=
    (Bool.and_eq_true_iff.mp hp).2
  have hlt (v : Fin 9) : pAt p v.val < 9 := by
    have hh := (List.all_eq_true.mp hp0) v.val (List.mem_range.mpr v.isLt)
    simpa using hh
  let f : Fin 9 → Fin 9 := fun v => ⟨pAt p v.val, hlt v⟩
  have hf : Function.Injective f := by
    intro v w h
    have hh := (List.all_eq_true.mp
      ((List.all_eq_true.mp hp1) v.val (List.mem_range.mpr v.isLt))) w.val
      (List.mem_range.mpr w.isLt)
    have he : pAt p v.val = pAt p w.val := congrArg Fin.val h
    have hv : v.val = w.val := by simpa [he] using hh
    exact Fin.ext hv
  let π : Equiv.Perm (Fin 9) := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  have hπ (v : Fin 9) : (π v).val = pAt p v.val := rfl
  have hrs := Sierksma.FB.relIdx_spec π p hπ
  let y' : Common.Partition 9 → ZMod 3 := fun Q => SplitSign π * y (Relabel π.symm Q)
  have hy' : SignedSystem y' := (Sierksma.signed_relabel y hy π).1
  have hsupp' (Q : Common.Partition 9) (hQ : y' Q ≠ 0) : Q ∈ Universe 3 := by
    have hn : y (Relabel π.symm Q) ≠ 0 := by
      intro hz
      exact hQ (by simp [y', hz])
    have hu := Sierksma.relabel_universe 3 π (Relabel π.symm Q) (hsupp _ hn)
    have hinv : Relabel π (Relabel π.symm Q) = Q := by
      simpa using (Sierksma.partition_relabel_inverse_type π.symm Q).1
    simpa only [hinv] using hu
  refine ⟨y', hy', hsupp', ?_⟩
  ext j
  constructor
  · intro hj
    have hjr : j < 1855 := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    have hjnz : y' (partOf j) ≠ 0 := (Finset.mem_filter.mp hj).2
    have hn : y (Relabel π.symm (partOf j)) ≠ 0 := by
      intro hz
      exact hjnz (by simp [y', hz])
    have hu := hsupp (Relabel π.symm (partOf j)) hn
    rw [← Sierksma.FB.partOf_bij.2.1] at hu
    obtain ⟨i, hir, hi⟩ := Finset.mem_image.mp hu
    have hir' : i < 1855 := Finset.mem_range.mp hir
    have hrel := (hrs.1 i hir').2
    have hinv : Relabel π (Relabel π.symm (partOf j)) = partOf j := by
      simpa using (Sierksma.partition_relabel_inverse_type π.symm (partOf j)).1
    have hparts : partOf (relIdx p i) = partOf j := by
      rw [hrel, hi, hinv]
    have heq := Sierksma.FB.partOf_bij.1 (relIdx p i) (hrs.1 i hir').1 j hjr hparts
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hir, by simpa only [hi] using hn⟩, heq⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hir : i < 1855 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hinz : y (partOf i) ≠ 0 := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (hrs.1 i hir).1, ?_⟩
    have hsupport := (Sierksma.signed_relabel y hy π).2
    have hmem : Relabel π (partOf i) ∈
        Finset.univ.filter (fun Q : Common.Partition 9 => y' Q ≠ 0) := by
      rw [hsupport]
      exact Finset.mem_image.mpr ⟨partOf i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinz⟩, rfl⟩
    have hn := (Finset.mem_filter.mp hmem).2
    simpa only [(hrs.1 i hir).2] using hn
