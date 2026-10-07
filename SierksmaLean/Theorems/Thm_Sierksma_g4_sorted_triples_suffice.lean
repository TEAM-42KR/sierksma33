import SierksmaLean.Proofs.Proof_Sierksma_g4_sorted_triples_suffice
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.g4_sorted_triples_suffice :
    ∀ (P : RQConfig) (h : ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9, StrictMono t → StrictMono t' → Disjoint (Endpoints e) (Finset.univ.image t) → Disjoint (Endpoints e) (Finset.univ.image t') → Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly P e t t' ≠ 0), ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9, Function.Injective t → Function.Injective t' → Disjoint (Endpoints e) (Finset.univ.image t) → Disjoint (Endpoints e) (Finset.univ.image t') → Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly P e t t' ≠ 0 :=
  @proof_Sierksma_g4_sorted_triples_suffice
