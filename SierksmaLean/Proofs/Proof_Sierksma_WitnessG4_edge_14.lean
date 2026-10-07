import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_rqtriple_det_formula
set_option autoImplicit false
open Sierksma
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000
theorem proof_Sierksma_WitnessG4_edge_14 : ∀ t t' : Fin 3 → Fin 9, StrictMono t → StrictMono t' →
    Disjoint (Endpoints ((1,4) : Edge 9)) (Finset.univ.image t) →
    Disjoint (Endpoints ((1,4) : Edge 9)) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly WitnessQ ((1,4) : Edge 9) t t' ≠ 0  := by
  have hc : ∀ t : Fin 3 → Fin 9, StrictMono t →
    Disjoint (Endpoints ((1,4) : Edge 9)) (Finset.univ.image t) →
    ∀ t' : Fin 3 → Fin 9, StrictMono t' →
    Disjoint (Endpoints ((1,4) : Edge 9)) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly WitnessQ ((1,4) : Edge 9) t t' ≠ 0 := by
    simp only [RQQPoly, Sierksma.rqtriple_det_formula, Pi.sub_apply]
    decide +kernel
  intro t t' ht ht' het het' htt'
  exact hc t ht het t' ht' het' htt'
