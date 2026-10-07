import SierksmaLean.Proofs.Proof_Sierksma_generic_witness_g1_sorted
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.generic_witness_g1_sorted :
    ∀ a : Fin 4 → Fin 9, StrictMono a → Matrix.det (fun i j : Fin 4 => RQLift WitnessQ (a i) j.val) ≠ 0 :=
  @proof_Sierksma_generic_witness_g1_sorted
