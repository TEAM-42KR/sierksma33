import SierksmaLean.Proofs.Proof_Sierksma_model_facet_certificate
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem Sierksma.model_facet_certificate :
    ∀ (a : Fin 4 → Fin 6)
 (B L U : Matrix (Fin 9) (Fin 9) ℚ) (p : Equiv.Perm (Fin 9)) (d : ℚ)
 (hd : 0<d)
 (hMB : ModelFacetMatrixQ a * B=(1 : Matrix (Fin 9) (Fin 9) ℚ))
 (hLU : (ModelFacetMatrixQ a).submatrix p id=L*U)
 (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular)
 (hdiag : (p.sign : ℚ)*(∏ i,L i i)*(∏ i,U i i)=d)
 (hB : ∀ i : Fin 9, B 8 i ≠ 0)
 (hpositive : (∀ i : Fin 9, 0<B 8 i) ↔ a=0), (ModelFacetMatrixQ a).det ≠ 0 ∧
 (∀ i, LastCofactorQ (ModelFacetMatrixQ a) i ≠ 0) ∧
 (if (ModelFacetMatrixQ a).det ≠ 0 ∧
   ∀ i,0<LastCofactorQ (ModelFacetMatrixQ a) i / (ModelFacetMatrixQ a).det
  then (SignType.sign (ModelFacetMatrixQ a).det : ℤ) else 0) =
 (if a=0 then 1 else 0) :=
  @proof_Sierksma_model_facet_certificate
