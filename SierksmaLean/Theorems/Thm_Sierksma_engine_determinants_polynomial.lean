import SierksmaLean.Proofs.Proof_Sierksma_engine_determinants_polynomial
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree Sierksma

theorem Sierksma.engine_determinants_polynomial :
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 72) ℝ, ∀ x : EngineParams,
      MvPolynomial.eval (fun i : Fin 72 => x ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).1 ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).2) p =
        augmentedDet (EngineMap x) s) ∧
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 72) ℝ, ∀ x : EngineParams,
      MvPolynomial.eval (fun i : Fin 72 => x ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).1 ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).2) p =
        linearDet (EngineMap x) s) :=
  @proof_Sierksma_engine_determinants_polynomial
