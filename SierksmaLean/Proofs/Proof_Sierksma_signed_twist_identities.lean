import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_coefficients_to_signed_system
import SierksmaLean.Theorems.Thm_Sierksma_twist_signed_polynomial
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem proof_Sierksma_signed_twist_identities :
    (∀ y : Common.Partition 9 → ZMod 3,
      (∀ pi : Equiv.Perm (Fin 9), IsSplitting pi → ∀ c : Fin 4 → ZMod 3,
        TwistPolynomial y pi c = 1) → SignedSystem y) ∧
    ∀ P ∈ GenericLocus, SignedSystem (TverbergSign P) := by
  refine ⟨Sierksma.coefficients_to_signed_system, ?_⟩
  intro P hP
  exact Sierksma.coefficients_to_signed_system (TverbergSign P)
    (fun pi hpi c => Sierksma.twist_signed_polynomial P hP pi hpi c)
