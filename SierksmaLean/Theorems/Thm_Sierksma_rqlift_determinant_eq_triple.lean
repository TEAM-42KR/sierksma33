import SierksmaLean.Proofs.Proof_Sierksma_rqlift_determinant_eq_triple
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.rqlift_determinant_eq_triple :
    ∀ (P : RQConfig) (u : Fin 9) (t : Fin 3 → Fin 9), Matrix.det (Matrix.of (fun i j : Fin 4 => RQLift P (![u,t 0,t 1,t 2] i) j.val)) = RQTripleDet P t (P u-P (t 0)) :=
  @proof_Sierksma_rqlift_determinant_eq_triple
