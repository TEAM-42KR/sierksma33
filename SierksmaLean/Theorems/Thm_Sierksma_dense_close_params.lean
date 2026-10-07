import SierksmaLean.Proofs.Proof_Sierksma_dense_close_params
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma

theorem Sierksma.dense_close_params :
    ∀ (S : Set EngineParams) (hS : Dense S) (x : EngineParams) (eps : ℝ) (heps : 0<eps), ∃ y ∈ S, CloseParams y x eps :=
  @proof_Sierksma_dense_close_params
