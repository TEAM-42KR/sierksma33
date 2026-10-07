import SierksmaLean.Definitions.Def_Sierksma_FBChecker
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col
import SierksmaLean.Theorems.Thm_Sierksma_FB_ternary_code_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_nine_list_bridge
import SierksmaLean.Theorems.Thm_Sierksma_FB_fibre_partition_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_indexed_partition_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_partition_ext_internal
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1000000

theorem proof_Sierksma_FB_colour_index_spec (c : Fin 9 → Fin 3) (hs : Function.Surjective c)
    (hc : ∀ a : Fin 3, ((Finset.univ : Finset (Fin 9)).filter (fun v => c v = a)).card ≤ 4) :
    let code := ∑ v : Fin 9, (c v).val * 3 ^ v.val
    idxOf code < 1855 ∧ partOf (idxOf code) =
      (Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun v : Fin 9 => c v = a)) := by
  classical
  let code := ∑ v : Fin 9, (c v).val * 3 ^ v.val
  have hcode : code < 19683 := (ternary_code_spec (fun v => (c v).val) (fun v => (c v).isLt)).1
  have hd (v : Fin 9) : digit3 code v.val = (c v).val :=
    (ternary_code_spec (fun v => (c v).val) (fun v => (c v).isLt)).2 v
  have hsurj : ∀ a < 3, ∃ v < 9, digit3 code v = a := by
    intro a ha
    obtain ⟨v,hv⟩ := hs ⟨a,ha⟩
    refine ⟨v.val,v.isLt,?_⟩
    rw [hd]; exact congrArg Fin.val hv
  have hsize : ∀ a < 3, ((List.range 9).filter (fun v => Nat.beq (digit3 code v) a)).length ≤ 4 := by
    intro a ha
    rw [(nine_list_bridge (digit3 code)).2 a]
    simp_rw [hd]
    simpa only [Fin.ext_iff,Fin.val_mk] using hc ⟨a,ha⟩
  have hj : idxOf code < 1855 := tab_col.2.2.2 code hcode hsurj hsize
  refine ⟨hj,?_⟩
  have hp := indexed_partition_spec (idxOf code) hj
  have hpart : IsPartition (partOf (idxOf code)) 3 := by
    exact (Finset.mem_filter.mp hp.1).2.1
  apply partition_ext_internal _ _ hpart (fibre_partition_spec c hs).1
  intro u v
  rw [hp.2.1 u v,(fibre_partition_spec c hs).2 u v]
  have ht := tab_col.2.2.1 code hcode hj u.val u.isLt v.val v.isLt
  simpa only [hd,Fin.ext_iff] using ht.symm
