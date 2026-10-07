import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open Common Sierksma

theorem proof_Sierksma_FB_sharedBlock_relabel (π : Equiv.Perm (Fin 9)) (Q : Common.Partition 9) (u v : Fin 9) :
 (∃ A ∈ Relabel π Q, π u ∈ A ∧ π v ∈ A) ↔ (∃ A ∈ Q, u ∈ A ∧ v ∈ A) := by
  classical
  have mem (w : Fin 9) (A : Block 9) : π w ∈ A.image π ↔ w ∈ A := by
    constructor
    · intro h
      obtain ⟨z,hz,hzw⟩ := Finset.mem_image.mp h
      exact π.injective hzw ▸ hz
    · intro h
      exact Finset.mem_image.mpr ⟨w,h,rfl⟩
  constructor
  · rintro ⟨A,hA,hu,hv⟩
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨B,hB,(mem u B).mp hu,(mem v B).mp hv⟩
  · rintro ⟨A,hA,hu,hv⟩
    exact ⟨A.image π,Finset.mem_image.mpr ⟨A,hA,rfl⟩,(mem u A).mpr hu,(mem v A).mpr hv⟩
