import SierksmaLean.Proofs.Proof_Sierksma_signed_twist_identities
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.signed_twist_identities :
    (∀ y : Common.Partition 9 → ZMod 3,
      (∀ pi : Equiv.Perm (Fin 9), IsSplitting pi → ∀ c : Fin 4 → ZMod 3,
        TwistPolynomial y pi c=1) → SignedSystem y) ∧
    ∀ P ∈ GenericLocus, SignedSystem (TverbergSign P) :=
  @proof_Sierksma_signed_twist_identities
