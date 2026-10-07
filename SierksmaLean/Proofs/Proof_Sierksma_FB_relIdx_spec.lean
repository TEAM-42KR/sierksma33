import SierksmaLean.Definitions.Def_Sierksma_FBChecker
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col
import SierksmaLean.Theorems.Thm_Sierksma_FB_partOf_bij
import SierksmaLean.Theorems.Thm_Sierksma_FB_indexed_partition_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_colour_index_spec
import SierksmaLean.Theorems.Thm_Sierksma_partition_relabel_inverse_type
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1000000

theorem proof_Sierksma_FB_relIdx_spec (π : Equiv.Perm (Fin 9)) (p : ℕ)
    (hp : ∀ v : Fin 9, (π v).val = pAt p v.val) :
    (∀ i < 1855, relIdx p i < 1855 ∧ partOf (relIdx p i) = Relabel π (partOf i)) ∧
    (∀ i < 1855, ∀ j < 1855, relIdx p i = relIdx p j → i = j) := by
  classical
  have spec : ∀ i < 1855, relIdx p i < 1855 ∧ partOf (relIdx p i) = Relabel π (partOf i) := by
    intro i hi
    have hb := (tab_col.1 i hi).2.1
    have hs := (tab_col.1 i hi).2.2.2.2.1
    let c : Fin 9 → Fin 3 := fun v => ⟨colOf i v.val,hb v.val v.isLt⟩
    let d : Fin 9 → Fin 3 := fun v => c (π.symm v)
    let B := fun a : Fin 3 => Finset.univ.filter (fun v : Fin 9 => c v = a)
    let D := fun a : Fin 3 => Finset.univ.filter (fun v : Fin 9 => d v = a)
    have eqi : partOf i = (Finset.univ : Finset (Fin 3)).image B := by
      unfold partOf
      congr 1
      funext a
      ext v
      simp [B,c,Fin.ext_iff]
    have sc : Function.Surjective c := by
      intro a
      obtain ⟨v,hv,hc⟩ := hs a.val a.isLt
      exact ⟨⟨v,hv⟩,Fin.ext hc⟩
    have sd : Function.Surjective d := by
      intro a
      obtain ⟨v,hv⟩ := sc a
      exact ⟨π v,by simpa [d] using hv⟩
    have fibres (a : Fin 3) : D a = (B a).image π := by
      ext v
      simp only [D,B,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
      constructor
      · intro h
        exact ⟨π.symm v,h,π.apply_symm_apply v⟩
      · rintro ⟨w,hw,rfl⟩
        simpa [d] using hw
    have hsize : ∀ a : Fin 3, (D a).card ≤ 4 := by
      intro a
      rw [fibres,Finset.card_image_of_injective _ π.injective]
      have hu := (Finset.mem_filter.mp (indexed_partition_spec i hi).1).2.2
      apply hu
      rw [eqi]
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
    have hd := colour_index_spec d sd hsize
    have hrel : relCode p i = ∑ v : Fin 9, colOf i v.val * 3 ^ (pAt p v.val) := by
      simp [relCode,List.range_succ,Fin.sum_univ_succ,Fin.succ]
      <;> omega
    have he : (∑ v : Fin 9, colOf i v.val * 3 ^ (pAt p v.val)) =
        ∑ v : Fin 9, (d v).val * 3 ^ v.val := by
      have hh := Equiv.sum_comp π (fun v : Fin 9 => (d v).val * 3 ^ v.val)
      simpa only [d,Equiv.symm_apply_apply,c,← hp] using hh
    have hcode : relCode p i = ∑ v : Fin 9, (d v).val * 3 ^ v.val := hrel.trans he
    refine ⟨?_,?_⟩
    · simpa only [relIdx,hcode] using hd.1
    · change partOf (idxOf (relCode p i)) = _
      rw [hcode,hd.2,eqi]
      simp only [Relabel,Finset.image_image]
      congr 1
      funext a
      exact fibres a
  refine ⟨spec,?_⟩
  intro i hi j hj hij
  have hre : Relabel π (partOf i) = Relabel π (partOf j) := by
    rw [← (spec i hi).2,← (spec j hj).2,hij]
  have hh := congrArg (Relabel π.symm) hre
  rw [(partition_relabel_inverse_type π (partOf i)).1,
    (partition_relabel_inverse_type π (partOf j)).1] at hh
  exact partOf_bij.1 i hi j hj hh
