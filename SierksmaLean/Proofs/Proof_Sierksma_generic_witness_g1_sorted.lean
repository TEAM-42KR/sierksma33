import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_PLDegree_det4_expansion
set_option autoImplicit false
open Sierksma
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem proof_Sierksma_generic_witness_g1_sorted : ∀ a : Fin 4 → Fin 9, StrictMono a →
    Matrix.det (fun i j : Fin 4 => RQLift WitnessQ (a i) j.val) ≠ 0 := by
  change ∀ a : Fin 4 → Fin 9, StrictMono a →
    (Matrix.of (fun i j : Fin 4 => RQLift WitnessQ (a i) j.val)).det ≠ 0
  simp only [PLDegree.det4_expansion]
  decide +kernel
