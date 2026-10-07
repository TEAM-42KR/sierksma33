import SierksmaLean.Theorems.Thm_Sierksma_generic_signed
import SierksmaLean.Theorems.Thm_Sierksma_finite_signed
import SierksmaLean.Theorems.Thm_Sierksma_count_lower_of_dense
import SierksmaLean.Theorems.Thm_Sierksma_classification
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma

theorem proof_Sierksma_main (P : Config 9 3) : 8 ≤ TverbergCount 3 P := by
  obtain ⟨D, hD, hDP⟩ := Sierksma.generic_signed
  refine Sierksma.count_lower_of_dense D hD 8 ?_ P
  intro P' hP'
  obtain ⟨hgp, hsys, hsupp⟩ := hDP P' hP'
  have hU : ∀ Q, TverbergSign P' Q ≠ 0 → Q ∈ Universe 3 := by
    intro Q hQ
    have hT : Q ∈ TverbergPartitions 3 P' := (hsupp Q).1 hQ
    have hT' : IsTverberg 3 P' Q := by
      simpa [TverbergPartitions] using hT
    obtain ⟨⟨hblocks, hcard⟩, hhull⟩ := hT'
    refine Sierksma.classification P' hgp Q ?_ hcard hhull
    rw [hblocks.2.2]
    exact hblocks
  have hset : (Universe 3).filter (fun Q => TverbergSign P' Q ≠ 0) = TverbergPartitions 3 P' := by
    ext Q
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact (hsupp Q).1 h
    · intro h
      exact ⟨hU Q ((hsupp Q).2 h), (hsupp Q).2 h⟩
  have h8 := Sierksma.finite_signed (TverbergSign P') hU hsys
  rw [hset] at h8
  exact h8
