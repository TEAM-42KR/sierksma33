import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open Common Sierksma
set_option maxHeartbeats 800000

theorem proof_Sierksma_FB_three_partition_colouring (Q : Common.Partition 9) (hQ : Common.IsPartition Q 3) :
    ∃ c : Fin 9 → Fin 3, Function.Surjective c ∧
      Q = (Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun v : Fin 9 => c v = a)) := by
  classical
  obtain ⟨⟨hne, hd, hcov⟩, hcard⟩ := hQ
  have existsB (v : Fin 9) : ∃ A : {A : Block 9 // A ∈ Q}, v ∈ A.val := by
    have hv : v ∈ Q.biUnion id := hcov.symm ▸ Finset.mem_univ v
    obtain ⟨A,hA,hvA⟩ := Finset.mem_biUnion.mp hv
    exact ⟨⟨A,hA⟩,hvA⟩
  let block (v : Fin 9) : {A : Block 9 // A ∈ Q} := Classical.choose (existsB v)
  have bv (v : Fin 9) : v ∈ (block v).val := Classical.choose_spec (existsB v)
  have unique (A B : {A : Block 9 // A ∈ Q}) (v : Fin 9)
      (hva : v ∈ A.val) (hvb : v ∈ B.val) : A = B := by
    apply Subtype.ext
    by_contra h
    exact Finset.disjoint_left.mp (hd A.val A.property B.val B.property h) hva hvb
  let e : {A : Block 9 // A ∈ Q} ≃ Fin 3 := Fintype.equivOfCardEq (by simpa using hcard)
  let c : Fin 9 → Fin 3 := fun v => e (block v)
  have fibre (a : Fin 3) : Finset.univ.filter (fun v : Fin 9 => c v = a) = (e.symm a).val := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h
      have hb : block v = e.symm a := e.injective (by simpa [c] using h)
      exact hb ▸ bv v
    · intro hv
      have hb := unique (block v) (e.symm a) v (bv v) hv
      simp [c,hb]
  refine ⟨c, ?_, ?_⟩
  · intro a
    obtain ⟨v,hv⟩ := (hne (e.symm a).val (e.symm a).property).1
    exact ⟨v, by have h := unique (block v) (e.symm a) v (bv v) hv; simp [c,h]⟩
  · ext A
    constructor
    · intro hA
      refine Finset.mem_image.mpr ⟨e ⟨A,hA⟩,Finset.mem_univ _,?_⟩
      rw [fibre]
      simp
    · intro hA
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
      rw [fibre]
      exact (e.symm a).property
