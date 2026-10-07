import SierksmaLean.Theorems.Thm_Sierksma_g4_sorted_triples_suffice
import SierksmaLean.Theorems.Thm_Sierksma_generic_witness_g4_sorted
set_option autoImplicit false
open Sierksma
theorem proof_Sierksma_generic_witness_g4 : ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9,
    Function.Injective t → Function.Injective t' →
    Disjoint (Endpoints e) (Finset.univ.image t) →
    Disjoint (Endpoints e) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly WitnessQ e t t' ≠ 0 :=
  Sierksma.g4_sorted_triples_suffice WitnessQ Sierksma.generic_witness_g4_sorted
