import SierksmaLean.Theorems.Thm_Sierksma_generic_locus_open_dense_of_nonempty
import SierksmaLean.Theorems.Thm_Sierksma_generic_locus_strong_gp
import SierksmaLean.Theorems.Thm_Sierksma_rational_generic_real_bridge
import SierksmaLean.Theorems.Thm_Sierksma_generic_witness_exact
set_option autoImplicit false
open Common Sierksma
theorem proof_Sierksma_generic_locus_dense :
    Dense GenericLocus ∧ IsOpen GenericLocus ∧
    (∀ P ∈ GenericLocus, StrongGP P) ∧ GenericWitnessExact ∧ WitnessReal ∈ GenericLocus := by
  have hw : GenericWitnessExact := Sierksma.generic_witness_exact
  have hr : WitnessReal ∈ GenericLocus := Sierksma.rational_generic_real_bridge WitnessQ hw
  obtain ⟨hd, ho⟩ := Sierksma.generic_locus_open_dense_of_nonempty ⟨WitnessReal, hr⟩
  exact ⟨hd, ho, Sierksma.generic_locus_strong_gp, hw, hr⟩
