import SierksmaLean.Proofs.Proof_Sierksma_generic_locus_dense
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.generic_locus_dense :
    Dense GenericLocus ∧ IsOpen GenericLocus ∧
    (∀ P ∈ GenericLocus, StrongGP P) ∧ GenericWitnessExact ∧ WitnessReal ∈ GenericLocus :=
  @proof_Sierksma_generic_locus_dense
