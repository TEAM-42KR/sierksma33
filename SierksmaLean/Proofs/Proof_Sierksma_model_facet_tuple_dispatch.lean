import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
theorem proof_Sierksma_model_facet_tuple_dispatch (h : ∀ q0 q1 q2 q3 : Fin 6, (ModelFacetMatrixQ ((![q0,q1,q2,q3] : Fin 4 → Fin 6))).det ≠ 0 ∧ (∀ i,LastCofactorQ (ModelFacetMatrixQ ((![q0,q1,q2,q3] : Fin 4 → Fin 6))) i ≠ 0) ∧ (if (ModelFacetMatrixQ ((![q0,q1,q2,q3] : Fin 4 → Fin 6))).det ≠ 0 ∧ (∀ i,0<LastCofactorQ (ModelFacetMatrixQ ((![q0,q1,q2,q3] : Fin 4 → Fin 6))) i / (ModelFacetMatrixQ ((![q0,q1,q2,q3] : Fin 4 → Fin 6))).det) then (SignType.sign (ModelFacetMatrixQ ((![q0,q1,q2,q3] : Fin 4 → Fin 6))).det : ℤ) else 0) = (if ((![q0,q1,q2,q3] : Fin 4 → Fin 6))=0 then 1 else 0)) : ∀ a : Fin 4 → Fin 6, (ModelFacetMatrixQ (a)).det ≠ 0 ∧ (∀ i,LastCofactorQ (ModelFacetMatrixQ (a)) i ≠ 0) ∧ (if (ModelFacetMatrixQ (a)).det ≠ 0 ∧ (∀ i,0<LastCofactorQ (ModelFacetMatrixQ (a)) i / (ModelFacetMatrixQ (a)).det) then (SignType.sign (ModelFacetMatrixQ (a)).det : ℤ) else 0) = (if (a)=0 then 1 else 0)  := by
  intro a
  have ha : a=![a 0,a 1,a 2,a 3] := by
    funext i
    fin_cases i <;> rfl
  simpa only [← ha] using h (a 0) (a 1) (a 2) (a 3)

