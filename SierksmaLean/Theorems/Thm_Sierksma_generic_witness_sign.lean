import SierksmaLean.Proofs.Proof_Sierksma_generic_witness_sign
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.generic_witness_sign :
    ∀ col : Fin 9 → ZMod 3, (∀ j : ZMod 3, (Finset.univ.filter (fun v => col v=j)).card ≤ 4) → (RQSignMatrix WitnessQ col).det ≠ 0 ∧ ∀ v, LastCofactorQ (RQSignMatrix WitnessQ col) v ≠ 0 :=
  @proof_Sierksma_generic_witness_sign
