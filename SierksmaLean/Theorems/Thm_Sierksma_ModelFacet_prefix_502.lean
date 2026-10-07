import SierksmaLean.Proofs.Proof_Sierksma_ModelFacet_prefix_502
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem Sierksma.ModelFacet.prefix_502 :
    ∀ q : Fin 6, (ModelFacetMatrixQ ((![5,0,2,q] : Fin 4 → Fin 6))).det ≠ 0 ∧ (∀ i,LastCofactorQ (ModelFacetMatrixQ ((![5,0,2,q] : Fin 4 → Fin 6))) i ≠ 0) ∧ (if (ModelFacetMatrixQ ((![5,0,2,q] : Fin 4 → Fin 6))).det ≠ 0 ∧ (∀ i,0<LastCofactorQ (ModelFacetMatrixQ ((![5,0,2,q] : Fin 4 → Fin 6))) i / (ModelFacetMatrixQ ((![5,0,2,q] : Fin 4 → Fin 6))).det) then (SignType.sign (ModelFacetMatrixQ ((![5,0,2,q] : Fin 4 → Fin 6))).det : ℤ) else 0) = (if ((![5,0,2,q] : Fin 4 → Fin 6))=0 then 1 else 0) :=
  @proof_Sierksma_ModelFacet_prefix_502
