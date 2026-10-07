import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open Common Sierksma

theorem proof_Sierksma_FB_partition_ext_internal (Q R : Common.Partition 9)
    (hQ : Common.IsPartition Q 3) (hR : Common.IsPartition R 3)
    (h : ∀ u v : Fin 9, (∃ A ∈ Q, u ∈ A ∧ v ∈ A) ↔ (∃ A ∈ R, u ∈ A ∧ v ∈ A)) : Q = R := by
  classical
  have sub (P T : Common.Partition 9) (hP : IsPartition P 3) (hT : IsPartition T 3)
      (hPT : ∀ u v : Fin 9, (∃ A ∈ P, u ∈ A ∧ v ∈ A) → (∃ A ∈ T, u ∈ A ∧ v ∈ A))
      (hTP : ∀ u v : Fin 9, (∃ A ∈ T, u ∈ A ∧ v ∈ A) → (∃ A ∈ P, u ∈ A ∧ v ∈ A)) : P ⊆ T := by
    intro A hA
    obtain ⟨v,hv⟩ := (hP.1.1 A hA).1
    obtain ⟨B,hB,hvB,_⟩ := hPT v v ⟨A,hA,hv,hv⟩
    have eq : A = B := by
      ext u
      constructor
      · intro hu
        obtain ⟨D,hD,huD,hvD⟩ := hPT u v ⟨A,hA,hu,hv⟩
        have hDB : D = B := by
          by_contra hne
          exact Finset.disjoint_left.mp (hT.1.2.1 D hD B hB hne) hvD hvB
        exact hDB ▸ huD
      · intro hu
        obtain ⟨D,hD,huD,hvD⟩ := hTP u v ⟨B,hB,hu,hvB⟩
        have hDA : D = A := by
          by_contra hne
          exact Finset.disjoint_left.mp (hP.1.2.1 D hD A hA hne) hvD hv
        exact hDA ▸ huD
    exact eq.symm ▸ hB
  exact Finset.Subset.antisymm
    (sub Q R hQ hR (fun u v => (h u v).mp) (fun u v => (h u v).mpr))
    (sub R Q hR hQ (fun u v => (h u v).mpr) (fun u v => (h u v).mp))
