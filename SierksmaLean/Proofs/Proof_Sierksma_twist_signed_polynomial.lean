import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_twist_polynomial_cone_count
import SierksmaLean.Theorems.Thm_Sierksma_test_map_perturbation_stability
set_option autoImplicit false
open Common Sierksma

theorem proof_Sierksma_twist_signed_polynomial (P : Config 9 3) (hP : P ∈ GenericLocus)
    (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3) :
    TwistPolynomial (TverbergSign P) pi c=1 := by
  rw [Sierksma.twist_polynomial_cone_count P hP pi hpi c]
  have hm := (Sierksma.test_map_perturbation_stability P hP pi hpi c).2
  change (ConeCount (TestParams P pi c) 0 : ZMod 3)=((1 : ℤ) : ZMod 3)
  rw [ZMod.intCast_eq_intCast_iff]
  change ConeCount (TestParams P pi c) 0 % 3 = 1 % 3
  simpa using hm
