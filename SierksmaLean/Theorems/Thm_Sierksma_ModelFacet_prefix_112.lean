import SierksmaLean.Proofs.Proof_Sierksma_ModelFacet_prefix_112
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem Sierksma.ModelFacet.prefix_112 :
    ∀ q : Fin 6, (ModelFacetMatrixQ ((![1,1,2,q] : Fin 4 → Fin 6))).det ≠ 0 ∧ (∀ i,LastCofactorQ (ModelFacetMatrixQ ((![1,1,2,q] : Fin 4 → Fin 6))) i ≠ 0) ∧ (if (ModelFacetMatrixQ ((![1,1,2,q] : Fin 4 → Fin 6))).det ≠ 0 ∧ (∀ i,0<LastCofactorQ (ModelFacetMatrixQ ((![1,1,2,q] : Fin 4 → Fin 6))) i / (ModelFacetMatrixQ ((![1,1,2,q] : Fin 4 → Fin 6))).det) then (SignType.sign (ModelFacetMatrixQ ((![1,1,2,q] : Fin 4 → Fin 6))).det : ℤ) else 0) = (if ((![1,1,2,q] : Fin 4 → Fin 6))=0 then 1 else 0) :=
  @proof_Sierksma_ModelFacet_prefix_112
