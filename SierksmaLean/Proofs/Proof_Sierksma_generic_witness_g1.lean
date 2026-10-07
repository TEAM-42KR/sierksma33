import SierksmaLean.Theorems.Thm_Sierksma_g1_sorted_determinants_suffice
import SierksmaLean.Theorems.Thm_Sierksma_generic_witness_g1_sorted
set_option autoImplicit false
open Sierksma
theorem proof_Sierksma_generic_witness_g1 : ∀ a : Fin 4 → Fin 9, Function.Injective a →
    Matrix.det (fun i j : Fin 4 => RQLift WitnessQ (a i) j.val) ≠ 0 :=
  Sierksma.g1_sorted_determinants_suffice WitnessQ Sierksma.generic_witness_g1_sorted
