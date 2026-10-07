import SierksmaLean.Proofs.Proof_Sierksma_generic_witness_g4_sorted
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.generic_witness_g4_sorted :
    ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9, StrictMono t → StrictMono t' → Disjoint (Endpoints e) (Finset.univ.image t) → Disjoint (Endpoints e) (Finset.univ.image t') → Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly WitnessQ e t t' ≠ 0 :=
  @proof_Sierksma_generic_witness_g4_sorted
