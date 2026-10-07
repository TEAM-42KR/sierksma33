import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree Sierksma
open scoped BigOperators

theorem proof_Sierksma_engine_determinants_polynomial :
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 72) ℝ, ∀ x : EngineParams,
      MvPolynomial.eval (fun i : Fin 72 => x ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).1 ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).2) p =
        augmentedDet (EngineMap x) s) ∧
    (∀ s : Finset ℕ, ∃ p : MvPolynomial (Fin 72) ℝ, ∀ x : EngineParams,
      MvPolynomial.eval (fun i : Fin 72 => x ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).1 ((finProdFinEquiv : Fin 9 × Fin 8 ≃ Fin 72).symm i).2) p =
        linearDet (EngineMap x) s) := by
  classical
  let e : Fin 9 × Fin 8 ≃ Fin 72 := finProdFinEquiv
  let z (x : EngineParams) (i : Fin 72) := x (e.symm i).1 (e.symm i).2
  let Y (r : Fin 9) (j : Fin 8) : MvPolynomial (Fin 72) ℝ := MvPolynomial.X (e (r,j))
  let PR (w : Fin 8 → MvPolynomial (Fin 72) ℝ) : Fin 8 → MvPolynomial (Fin 72) ℝ := fun j =>
    if h : j.val<4 then -w ⟨j.val+4,by omega⟩ else w ⟨j.val-4,by omega⟩-w j
  let E (v : ℕ) : Fin 8 → MvPolynomial (Fin 72) ℝ :=
    if h : v<24 then (PR^[v%6/2]) (Y ⟨2*(v/6)+v%2,by omega⟩)
    else if h' : v<27 then (PR^[v-24]) (Y 8) else 0
  have hPR : ∀ x w, (fun j => MvPolynomial.eval (z x) (PR w j)) =
      R8 (fun j => MvPolynomial.eval (z x) (w j)) := by
    intro x w
    funext j
    dsimp [PR,R8]
    split_ifs <;> simp
  have hpow : ∀ (k : ℕ) x w,
      (fun j => MvPolynomial.eval (z x) ((PR^[k]) w j)) =
        (R8^[k]) (fun j => MvPolynomial.eval (z x) (w j)) := by
    intro k
    induction k with
    | zero => intro x w; rfl
    | succ k ih =>
      intro x w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hPR x _).trans (congrArg R8 (ih x w))
  have hE : ∀ x v j, MvPolynomial.eval (z x) (E v j)=EngineMap x v j := by
    intro x v j
    unfold EngineMap RPower
    dsimp [E]
    split_ifs
    · have hh := congrFun (hpow (v%6/2) x (Y ⟨2*(v/6)+v%2,by omega⟩)) j
      simpa [Y,z] using hh
    · have hh := congrFun (hpow (v-24) x (Y 8)) j
      simpa [Y,z] using hh
    · simp
  constructor
  · intro s
    by_cases hs : s.card=9
    · let M : Matrix (Fin 9) (Fin 9) (MvPolynomial (Fin 72) ℝ) := fun i j =>
        if hj : j.val<8 then E (s.orderEmbOfFin hs i) ⟨j.val,hj⟩ else 1
      refine ⟨M.det, ?_⟩
      intro x
      change MvPolynomial.eval (z x) M.det = _
      rw [RingHom.map_det]
      rw [augmentedDet, dif_pos hs]
      congr 1
      ext i j
      change MvPolynomial.eval (z x) (M i j) =
        augment (EngineMap x (s.orderEmbOfFin hs i)) 1 j
      dsimp [M,augment]
      split_ifs <;> simp [hE]
    · refine ⟨0,?_⟩
      intro x
      simp [augmentedDet,hs]
  · intro s
    by_cases hs : s.card=8
    · let M : Matrix (Fin 8) (Fin 8) (MvPolynomial (Fin 72) ℝ) := fun i j =>
        E (s.orderEmbOfFin hs i) j
      refine ⟨M.det,?_⟩
      intro x
      change MvPolynomial.eval (z x) M.det = _
      rw [RingHom.map_det]
      rw [linearDet, dif_pos hs]
      congr 1
      ext i j
      exact hE x _ _
    · refine ⟨0,?_⟩
      intro x
      simp [linearDet,hs]
