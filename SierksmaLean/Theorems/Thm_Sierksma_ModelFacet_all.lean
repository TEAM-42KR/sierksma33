import SierksmaLean.Proofs.Proof_Sierksma_ModelFacet_all
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem Sierksma.ModelFacet.all :
    ∀ a : Fin 4 → Fin 6, (ModelFacetMatrixQ (a)).det ≠ 0 ∧ (∀ i,LastCofactorQ (ModelFacetMatrixQ (a)) i ≠ 0) ∧ (if (ModelFacetMatrixQ (a)).det ≠ 0 ∧ (∀ i,0<LastCofactorQ (ModelFacetMatrixQ (a)) i / (ModelFacetMatrixQ (a)).det) then (SignType.sign (ModelFacetMatrixQ (a)).det : ℤ) else 0) = (if (a)=0 then 1 else 0) :=
  @proof_Sierksma_ModelFacet_all
