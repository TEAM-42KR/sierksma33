import SierksmaLean.Proofs.Proof_Sierksma_coefficients_to_signed_system
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.coefficients_to_signed_system :
    ∀ (y : Common.Partition 9 → ZMod 3)
    (h : ∀ pi : Equiv.Perm (Fin 9), IsSplitting pi → ∀ c : Fin 4 → ZMod 3, TwistPolynomial y pi c = 1), SignedSystem y :=
  @proof_Sierksma_coefficients_to_signed_system
