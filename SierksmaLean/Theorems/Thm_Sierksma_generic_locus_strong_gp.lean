import SierksmaLean.Proofs.Proof_Sierksma_generic_locus_strong_gp
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma

theorem Sierksma.generic_locus_strong_gp :
    ∀ P ∈ GenericLocus, StrongGP P :=
  @proof_Sierksma_generic_locus_strong_gp
