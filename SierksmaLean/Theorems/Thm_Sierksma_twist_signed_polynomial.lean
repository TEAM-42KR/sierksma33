import SierksmaLean.Proofs.Proof_Sierksma_twist_signed_polynomial
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.twist_signed_polynomial :
    ∀ (P : Config 9 3) (hP : P ∈ GenericLocus)
    (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3), TwistPolynomial (TverbergSign P) pi c=1 :=
  @proof_Sierksma_twist_signed_polynomial
