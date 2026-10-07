import SierksmaLean.Proofs.Proof_Sierksma_rational_generic_real_bridge
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma

theorem Sierksma.rational_generic_real_bridge :
    ∀ (P : RQConfig) (h : RationalGenericCheck P), (fun v j => (P v j : ℝ)) ∈ GenericLocus :=
  @proof_Sierksma_rational_generic_real_bridge
