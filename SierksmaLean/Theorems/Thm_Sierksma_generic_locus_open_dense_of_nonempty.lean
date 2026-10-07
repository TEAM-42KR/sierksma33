import SierksmaLean.Proofs.Proof_Sierksma_generic_locus_open_dense_of_nonempty
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma

theorem Sierksma.generic_locus_open_dense_of_nonempty :
    ∀ (h : GenericLocus.Nonempty), Dense GenericLocus ∧ IsOpen GenericLocus :=
  @proof_Sierksma_generic_locus_open_dense_of_nonempty
