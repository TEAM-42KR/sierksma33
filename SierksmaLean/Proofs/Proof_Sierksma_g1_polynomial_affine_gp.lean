import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Common Sierksma
open scoped BigOperators

theorem proof_Sierksma_g1_polynomial_affine_gp (P : Config 9 3) (h : G1Polynomial P) : AffineGP P := by
  classical
  have h4 (a : Fin 4 → Fin 9) (ha : Function.Injective a) :
      AffineIndependent ℝ (fun i => P (a i)) := by
    let M : Matrix (Fin 4) (Fin 4) ℝ := fun i j => LiftCoord P (a i) j.val
    have hind : LinearIndependent ℝ (fun i => M i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero (h a ha)
    rw [affineIndependent_iff]
    intro s w hs hw
    have hm : ∑ i ∈ s, w i • M i = 0 := by
      ext j
      by_cases hj : j.val < 3
      · have he := congrFun hw ⟨j.val, hj⟩
        simpa [M, LiftCoord, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he
      · simpa [M, LiftCoord, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs
    exact (linearIndependent_iff'.mp hind) s w hm
  intro A hA
  obtain ⟨B, hAB, hBu, hB⟩ := Finset.exists_subsuperset_card_eq
    (show A ⊆ Finset.univ from Finset.subset_univ A) hA
    (show 4 ≤ (Finset.univ : Finset (Fin 9)).card by decide)
  let e : B ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using hB)
  let a : Fin 4 → Fin 9 := fun i => (e.symm i).val
  have ha : Function.Injective a := Subtype.val_injective.comp e.symm.injective
  have hBi : AffineIndependent ℝ (fun v : B => P v.val) := by
    convert (h4 a ha).comp_embedding e.toEmbedding using 1
    ext v
    simp [a, Function.comp_def]
  let f : A ↪ B := ⟨fun v => ⟨v.val, hAB v.property⟩, by
    intro v v' he
    exact Subtype.ext (congrArg (fun z : B => z.val) he)⟩
  exact hBi.comp_embedding f
