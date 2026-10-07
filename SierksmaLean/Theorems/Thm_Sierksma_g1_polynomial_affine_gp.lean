import SierksmaLean.Proofs.Proof_Sierksma_g1_polynomial_affine_gp
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma

theorem Sierksma.g1_polynomial_affine_gp :
    ∀ (P : Config 9 3) (h : G1Polynomial P), AffineGP P :=
  @proof_Sierksma_g1_polynomial_affine_gp
