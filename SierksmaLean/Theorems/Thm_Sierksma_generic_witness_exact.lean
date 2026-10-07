import SierksmaLean.Proofs.Proof_Sierksma_generic_witness_exact
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.generic_witness_exact :
    GenericWitnessExact :=
  @proof_Sierksma_generic_witness_exact
