import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open Common Sierksma
set_option maxHeartbeats 800000

theorem proof_Sierksma_FB_fibre_partition_spec (c : Fin 9 → Fin 3) (hs : Function.Surjective c) :
    let Q := (Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun v : Fin 9 => c v = a))
    Common.IsPartition Q 3 ∧ ∀ u v : Fin 9, (∃ A ∈ Q, u ∈ A ∧ v ∈ A) ↔ c u = c v := by
  classical
  let B := fun a : Fin 3 => Finset.univ.filter (fun v : Fin 9 => c v = a)
  have mem (v : Fin 9) (a : Fin 3) : v ∈ B a ↔ c v = a := by simp [B]
  have ne (a : Fin 3) : (B a).Nonempty := by
    obtain ⟨v, hv⟩ := hs a
    exact ⟨v, (mem v a).mpr hv⟩
  have inj : Function.Injective B := by
    intro a b hab
    obtain ⟨v,hv⟩ := ne a
    have hvb := hab ▸ hv
    exact ((mem v a).mp hv).symm.trans ((mem v b).mp hvb)
  constructor
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro A hA
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
      exact ⟨ne a, Finset.subset_univ _⟩
    · intro A hA D hD hAD
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hD
      apply Finset.disjoint_left.mpr
      intro v hva hvb
      have hab : a = b := ((mem v a).mp hva).symm.trans ((mem v b).mp hvb)
      exact hAD (congrArg B hab)
    · ext v
      simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
      exact ⟨B (c v), Finset.mem_image.mpr ⟨c v, Finset.mem_univ _, rfl⟩, (mem v (c v)).mpr rfl⟩
    · rw [Finset.card_image_of_injective _ inj]
      decide
  · intro u v
    constructor
    · rintro ⟨A,hA,hu,hv⟩
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
      exact ((mem u a).mp hu).trans ((mem v a).mp hv).symm
    · intro huv
      exact ⟨B (c u), Finset.mem_image.mpr ⟨c u, Finset.mem_univ _, rfl⟩,
        (mem u (c u)).mpr rfl, (mem v (c u)).mpr huv.symm⟩
