import SierksmaLean.Theorems.Thm_PLDegree_lu_determinant_certificate
import SierksmaLean.Theorems.Thm_Sierksma_last_cofactor_ratio_certificate
set_option autoImplicit false
open Sierksma
open scoped BigOperators
theorem proof_Sierksma_model_facet_certificate (a : Fin 4 → Fin 6)
 (B L U : Matrix (Fin 9) (Fin 9) ℚ) (p : Equiv.Perm (Fin 9)) (d : ℚ)
 (hd : 0<d)
 (hMB : ModelFacetMatrixQ a * B=(1 : Matrix (Fin 9) (Fin 9) ℚ))
 (hLU : (ModelFacetMatrixQ a).submatrix p id=L*U)
 (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular)
 (hdiag : (p.sign : ℚ)*(∏ i,L i i)*(∏ i,U i i)=d)
 (hB : ∀ i : Fin 9, B 8 i ≠ 0)
 (hpositive : (∀ i : Fin 9, 0<B 8 i) ↔ a=0) :
 (ModelFacetMatrixQ a).det ≠ 0 ∧
 (∀ i, LastCofactorQ (ModelFacetMatrixQ a) i ≠ 0) ∧
 (if (ModelFacetMatrixQ a).det ≠ 0 ∧
   ∀ i,0<LastCofactorQ (ModelFacetMatrixQ a) i / (ModelFacetMatrixQ a).det
  then (SignType.sign (ModelFacetMatrixQ a).det : ℤ) else 0) =
 (if a=0 then 1 else 0)  := by
  let M := ModelFacetMatrixQ a
  have hdet : M.det=d := PLDegree.lu_determinant_certificate M L U p d hLU hL hU hdiag
  have hm : M.det ≠ 0 := by rw [hdet]; exact ne_of_gt hd
  obtain ⟨_,hc⟩ := Sierksma.last_cofactor_ratio_certificate M B 1 (by norm_num) (by simpa using hMB)
  simp only [div_one] at hc
  refine ⟨hm,?_,?_⟩
  · intro i
    intro hz
    have hh := hc i
    rw [hz,zero_div] at hh
    exact hB i hh.symm
  · have hp : (∀ i,0<LastCofactorQ M i / M.det) ↔ a=0 := by
      simpa only [hc] using hpositive
    have hs : (SignType.sign M.det : ℤ)=1 := by
      rw [hdet,sign_pos hd]
      rfl
    change (if M.det ≠ 0 ∧ (∀ i,0<LastCofactorQ M i / M.det)
      then (SignType.sign M.det : ℤ) else 0) = (if a=0 then 1 else 0)
    have hi : (M.det ≠ 0 ∧ (∀ i,0<LastCofactorQ M i / M.det)) ↔ a=0 :=
      (and_iff_right hm).trans hp
    by_cases hz : a=0
    · rw [if_pos (hi.mpr hz),if_pos hz]
      exact hs
    · rw [if_neg (mt hi.mp hz),if_neg hz]

