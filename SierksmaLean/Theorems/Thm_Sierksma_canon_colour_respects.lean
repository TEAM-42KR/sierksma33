import SierksmaLean.Proofs.Proof_Sierksma_canon_colour_respects
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.canon_colour_respects :
    ∀ {n : ℕ} (Q : Common.Partition n)
    (hQ : IsPartition Q 3), Respects Q (CanonColour Q) :=
  @proof_Sierksma_canon_colour_respects
