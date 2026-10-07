import SierksmaLean.Theorems.Thm_Sierksma_partition_relabel_inverse_type
set_option autoImplicit false
open Sierksma Common

theorem proof_Sierksma_relabel_universe (d : ℕ)
    (p : Equiv.Perm (Fin (N d))) (Q : Common.Partition (N d))
    (hQ : Q ∈ Universe d) : Relabel p Q ∈ Universe d := by
  classical
  have hh : IsPartition Q 3 ∧ ∀ A ∈ Q, A.card ≤ d + 1 := (Finset.mem_filter.mp hQ).2
  rcases hh with ⟨⟨⟨hne, hdis, hunion⟩, hcard⟩, hbound⟩
  have hcardA (A : Block (N d)) : (A.image p).card = A.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => p.injective h)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro A' hA'
      rcases Finset.mem_image.mp hA' with ⟨A, hA, rfl⟩
      exact ⟨(hne A hA).1.image p, Finset.subset_univ _⟩
    · intro A' hA' B' hB' hneAB
      rcases Finset.mem_image.mp hA' with ⟨A, hA, rfl⟩
      rcases Finset.mem_image.mp hB' with ⟨B, hB, rfl⟩
      have hn : A ≠ B := fun h => hneAB (congrArg (Finset.image p) h)
      apply Finset.disjoint_left.mpr
      intro x hx hy
      rcases Finset.mem_image.mp hx with ⟨a, ha, hax⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, hbx⟩
      have hab : a = b := p.injective (hax.trans hbx.symm)
      subst b
      exact Finset.disjoint_left.mp (hdis A hA B hB hn) ha hb
    · apply Finset.ext
      intro x
      constructor
      · intro _
        exact Finset.mem_univ _
      · intro _
        have hx : p.symm x ∈ Q.biUnion id := by rw [hunion]; exact Finset.mem_univ _
        rcases Finset.mem_biUnion.mp hx with ⟨A, hA, hxA⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨A.image p, Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨p.symm x, hxA, p.apply_symm_apply x⟩
  · have ht := (partition_relabel_inverse_type p Q).2
    have hc : (Relabel p Q).card = Q.card := by simpa using congrArg Multiset.card ht
    exact hc.trans hcard
  · intro A' hA'
    rcases Finset.mem_image.mp hA' with ⟨A, hA, rfl⟩
    rw [hcardA]
    exact hbound A hA
