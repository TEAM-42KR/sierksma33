import SierksmaLean.Theorems.Thm_Sierksma_generic_locus_dense
import SierksmaLean.Theorems.Thm_Sierksma_signed_twist_identities
import SierksmaLean.Theorems.Thm_Sierksma_test_map_zero_equivalence
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem proof_Sierksma_generic_signed : ∃ D : Set (Config 9 3), Dense D ∧
    ∀ P ∈ D, StrongGP P ∧ SignedSystem (TverbergSign P) ∧
      ∀ Q : Common.Partition 9, TverbergSign P Q ≠ 0 ↔ Q ∈ TverbergPartitions 3 P := by
  refine ⟨GenericLocus, Sierksma.generic_locus_dense.1, ?_⟩
  intro P hP
  refine ⟨Sierksma.generic_locus_dense.2.2.1 P hP,
    Sierksma.signed_twist_identities.2 P hP, ?_⟩
  exact Sierksma.test_map_zero_equivalence.2.2.2 P hP
