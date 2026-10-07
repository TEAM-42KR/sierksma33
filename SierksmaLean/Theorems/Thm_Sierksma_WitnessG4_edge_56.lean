import SierksmaLean.Proofs.Proof_Sierksma_WitnessG4_edge_56
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.WitnessG4.edge_56 :
    ∀ t t' : Fin 3 → Fin 9, StrictMono t → StrictMono t' →
    Disjoint (Endpoints ((5,6) : Edge 9)) (Finset.univ.image t) →
    Disjoint (Endpoints ((5,6) : Edge 9)) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly WitnessQ ((5,6) : Edge 9) t t' ≠ 0 :=
  @proof_Sierksma_WitnessG4_edge_56
