import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_canon_colour_respects
set_option autoImplicit false
open Common Sierksma
open scoped BigOperators

theorem proof_Sierksma_rational_generic_real_bridge (P : RQConfig) (h : RationalGenericCheck P) :
    (fun v j => (P v j : ℝ)) ∈ GenericLocus := by
  classical
  let R : Config 9 3 := fun v j => (P v j : ℝ)
  have hlift (v : Fin 9) (j : ℕ) : (RQLift P v j : ℝ) = LiftCoord R v j := by
    unfold RQLift LiftCoord
    split_ifs <;> simp [R]
  have htriple (t : Fin 3 → Fin 9) (q : Fin 3 → ℚ) :
      (RQTripleDet P t q : ℝ) = TripleDet R t (fun j => (q j : ℝ)) := by
    let M : Matrix (Fin 3) (Fin 3) ℚ := ![P (t 1)-P (t 0), P (t 2)-P (t 0), q]
    have hm : M.map (Rat.castHom ℝ) = ![R (t 1)-R (t 0), R (t 2)-R (t 0), (fun j => (q j : ℝ))] := by
      ext i j
      change ((M i j : ℚ) : ℝ) = _
      fin_cases i <;> simp [M, R]
    exact ((Rat.castHom ℝ).map_det M).trans (congrArg Matrix.det hm)
  have hq (e : Edge 9) (t t' : Fin 3 → Fin 9) :
      (RQQPoly P e t t' : ℝ) = QPoly R e t t' := by
    unfold RQQPoly QPoly
    push_cast
    rw [htriple, htriple, htriple, htriple]
    simp only [Pi.sub_apply, Rat.cast_sub]
    rfl
  have hm (col : Fin 9 → ZMod 3) :
      (RQSignMatrix P col).map ((↑) : ℚ → ℝ) = SignMatrix R col := by
    ext v j
    change (RQSignMatrix P col v j : ℝ) = SignRow R col v j
    unfold RQSignMatrix SignRow
    split_ifs <;> simp [hlift]
  have hd (col : Fin 9 → ZMod 3) :
      ((RQSignMatrix P col).det : ℝ) = (SignMatrix R col).det := by
    exact ((Rat.castHom ℝ).map_det (RQSignMatrix P col)).trans (congrArg Matrix.det (hm col))
  have hc (M : Matrix (Fin 9) (Fin 9) ℚ) (v : Fin 9) :
      (LastCofactorQ M v : ℝ) = LastCofactor (M.map ((↑) : ℚ → ℝ)) v := by
    change (((-1 : ℚ) ^ (v.val+8) * Matrix.det (fun r c : Fin 8 => M (v.succAbove r) c.castSucc) : ℚ) : ℝ) = _
    rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
    exact congrArg (fun z : ℝ => (-1)^ (v.val+8) * z)
      ((Rat.castHom ℝ).map_det (fun r c : Fin 8 => M (v.succAbove r) c.castSucc))
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    have hz := h.1 a ha
    let M : Matrix (Fin 4) (Fin 4) ℚ := fun i j => RQLift P (a i) j.val
    have he : (M.det : ℝ) = Matrix.det (fun i j : Fin 4 => LiftCoord R (a i) j.val) := by
      have hm : M.map (Rat.castHom ℝ) = (fun i j : Fin 4 => LiftCoord R (a i) j.val) := by
        ext i j
        exact hlift _ _
      exact ((Rat.castHom ℝ).map_det M).trans (congrArg Matrix.det hm)
    rw [← he]
    exact_mod_cast hz
  · intro e he t t' ht ht' het het' htt'
    rw [← hq]
    exact_mod_cast h.2.1 e he t t' ht ht' het het' htt'
  · intro Q hQ
    have hQ' : IsPartition Q 3 ∧ ∀ A ∈ Q, A.card ≤ 4 := by
      simpa [Universe] using hQ
    have hres := Sierksma.canon_colour_respects Q hQ'.1
    have hsize : ∀ j : ZMod 3,
        (Finset.univ.filter (fun v => CanonColour Q v = j)).card ≤ 4 := by
      intro j
      let S := Finset.univ.filter (fun v => CanonColour Q v = j)
      by_cases hn : S.Nonempty
      · obtain ⟨v, hv⟩ := hn
        have hvj : CanonColour Q v = j := (Finset.mem_filter.mp hv).2
        have hvu : v ∈ Q.biUnion id := by rw [hQ'.1.1.2.2]; simp
        obtain ⟨A, hAQ, hvA⟩ := Finset.mem_biUnion.mp hvu
        have hSA : S ⊆ A := by
          intro u hu
          have huj : CanonColour Q u = j := (Finset.mem_filter.mp hu).2
          obtain ⟨B, hBQ, huB, hvB⟩ := (hres u v).mp (huj.trans hvj.symm)
          have hBA : B = A := by
            by_contra hne
            exact Finset.disjoint_left.mp (hQ'.1.1.2.1 B hBQ A hAQ hne) hvB hvA
          simpa [hBA] using huB
        exact (Finset.card_le_card hSA).trans (hQ'.2 A hAQ)
      · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        simp only [show Finset.univ.filter (fun v => CanonColour Q v = j) = S from rfl, he,
          Finset.card_empty, zero_le]
    have hs := h.2.2 (CanonColour Q) hsize
    constructor
    · rw [← hd]
      exact_mod_cast hs.1
    · intro v
      rw [← hm, ← hc]
      exact_mod_cast hs.2 v
