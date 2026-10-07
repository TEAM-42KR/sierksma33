import SierksmaLean.Proofs.Proof_Sierksma_twist_polynomial_cone_count
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common PLDegree Sierksma

theorem Sierksma.twist_polynomial_cone_count :
    ∀ (P : Config 9 3) (hP : P ∈ GenericLocus) (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3), TwistPolynomial (TverbergSign P) pi c=(ConeCount (TestParams P pi c) 0 : ZMod 3) :=
  @proof_Sierksma_twist_polynomial_cone_count
