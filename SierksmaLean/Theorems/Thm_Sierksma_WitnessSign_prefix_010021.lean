import SierksmaLean.Proofs.Proof_Sierksma_WitnessSign_prefix_010021
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.WitnessSign.prefix_010021 :
    ∀ x y z : ZMod 3, (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![0,1,0,0,2,1,x,y,z] : Fin 9 → ZMod 3) v=j)).card ≤ 4) → (RQSignMatrix WitnessQ (![0,1,0,0,2,1,x,y,z] : Fin 9 → ZMod 3)).det ≠ 0 ∧ ∀ v, LastCofactorQ (RQSignMatrix WitnessQ (![0,1,0,0,2,1,x,y,z] : Fin 9 → ZMod 3)) v ≠ 0 :=
  @proof_Sierksma_WitnessSign_prefix_010021
