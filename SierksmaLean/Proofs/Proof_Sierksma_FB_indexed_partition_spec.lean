import SierksmaLean.Definitions.Def_Sierksma_FBChecker
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col
import SierksmaLean.Theorems.Thm_Sierksma_FB_fibre_partition_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_rgs_canonical
import SierksmaLean.Theorems.Thm_Sierksma_FB_nine_list_bridge
set_option autoImplicit false
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1000000

theorem proof_Sierksma_FB_indexed_partition_spec (i : ℕ) (hi : i < 1855) :
    partOf i ∈ Universe 3 ∧
    (∀ u v : Fin 9, (∃ A ∈ partOf i, u ∈ A ∧ v ∈ A) ↔ colOf i u.val = colOf i v.val) ∧
    (∀ v : Fin 9, CanonColour (partOf i) v = ((colOf i v.val : ℕ) : ZMod 3)) := by
  classical
  obtain ⟨hword,hb,hzero,hr,hs,hsize⟩ := tab_col.1 i hi
  let c : Fin 9 → Fin 3 := fun v => ⟨colOf i v.val,hb v.val v.isLt⟩
  have cv (v : Fin 9) : (c v).val = colOf i v.val := rfl
  have surj : Function.Surjective c := by
    intro a
    obtain ⟨v,hv,hc⟩ := hs a.val a.isLt
    exact ⟨⟨v,hv⟩, Fin.ext hc⟩
  have eq : partOf i = (Finset.univ : Finset (Fin 3)).image
      (fun a => Finset.univ.filter (fun v : Fin 9 => c v = a)) := by
    unfold partOf
    congr 1
    funext a
    ext v
    simp [c,Fin.ext_iff]
  have spec := fibre_partition_spec c surj
  rw [← eq] at spec
  have rg : ∀ v : Fin 9, 0 < (c v).val → ∃ w : Fin 9, w < v ∧ (c w).val + 1 = (c v).val := by
    intro v hv
    obtain ⟨w,hw,hc⟩ := hr v.val v.isLt (c v).val (c v).isLt rfl hv
    exact ⟨⟨w,lt_trans hw v.isLt⟩, hw, hc⟩
  have can := rgs_canonical c surj rg
  rw [← eq] at can
  refine ⟨?_,?_,can⟩
  · simp only [Universe,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨spec.1,?_⟩
    intro A hA
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp (eq ▸ hA)
    have h := hsize a.val a.isLt
    rw [(nine_list_bridge (colOf i)).2 a.val] at h
    have ef : (Finset.univ.filter (fun v : Fin 9 => colOf i v.val = a.val)) =
        Finset.univ.filter (fun v : Fin 9 => c v = a) := by
      ext v; simp [c,Fin.ext_iff]
    rw [ef] at h
    exact h
  · intro u v
    simpa only [Fin.ext_iff,cv] using spec.2 u v
