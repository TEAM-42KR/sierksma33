import SierksmaLean.Definitions.Def_Sierksma_FBChecker
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col
import SierksmaLean.Theorems.Thm_Sierksma_FB_indexed_partition_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_colour_index_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_three_partition_colouring
import SierksmaLean.Theorems.Thm_Sierksma_FB_nine_list_bridge
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1000000

theorem proof_Sierksma_FB_partOf_bij :
    (∀ i < 1855, ∀ j < 1855, partOf i = partOf j → i = j) ∧
    (Finset.range 1855).image partOf = Universe 3 ∧
    (∀ i < 1855, ∀ v : Fin 9, CanonColour (partOf i) v = ((colOf i v.val : ℕ) : ZMod 3)) := by
  classical
  have inj : ∀ i < 1855, ∀ j < 1855, partOf i = partOf j → i = j := by
    intro i hi j hj hij
    have hc (v : Fin 9) : colOf i v.val = colOf j v.val := by
      have h : ((colOf i v.val : ℕ) : ZMod 3) = ((colOf j v.val : ℕ) : ZMod 3) := by
        rw [← (indexed_partition_spec i hi).2.2 v, ← (indexed_partition_spec j hj).2.2 v, hij]
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast_of_lt ((tab_col.1 i hi).2.1 v.val v.isLt),
        ZMod.val_natCast_of_lt ((tab_col.1 j hj).2.1 v.val v.isLt)] using hv
    have he : (∑ v : Fin 9, colOf i v.val * 3 ^ v.val) = (∑ v : Fin 9, colOf j v.val * 3 ^ v.val) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hc]
    have hti := tab_col.2.1 i hi
    have htj := tab_col.2.1 j hj
    rw [(nine_list_bridge (colOf i)).1] at hti
    rw [(nine_list_bridge (colOf j)).1] at htj
    rw [← hti, ← htj, he]
  refine ⟨inj, ?_, fun i hi => (indexed_partition_spec i hi).2.2⟩
  ext Q
  constructor
  · intro hQ
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
    exact (indexed_partition_spec i (Finset.mem_range.mp hi)).1
  · intro hQ
    have hu : IsPartition Q 3 ∧ ∀ A ∈ Q, A.card ≤ 4 := (Finset.mem_filter.mp hQ).2
    obtain ⟨c,hs,hc⟩ := three_partition_colouring Q hu.1
    have hsize : ∀ a : Fin 3, ((Finset.univ : Finset (Fin 9)).filter (fun v => c v = a)).card ≤ 4 := by
      intro a
      apply hu.2
      rw [hc]
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    have hi := colour_index_spec c hs hsize
    refine Finset.mem_image.mpr ⟨idxOf (∑ v : Fin 9, (c v).val * 3 ^ v.val), Finset.mem_range.mpr hi.1, ?_⟩
    exact hi.2.trans hc.symm
