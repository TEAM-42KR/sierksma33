import SierksmaLean.Theorems.Thm_Sierksma_engine_determinants_polynomial
import SierksmaLean.Theorems.Thm_PLDegree_polynomial_nonzero_open_dense
set_option autoImplicit false
open PLDegree Sierksma
open scoped BigOperators

theorem proof_Sierksma_engine_generic_prefix_auxiliary (x y : EngineParams) (hx : EngineGeneric x) (hy : EngineGeneric y) :
    ∃ z : EngineParams, (∀ t : Fin 10,
      EngineGeneric (fun r => if r.val<t.val then z r else x r)) ∧
      (∀ t : Fin 10, EngineGeneric (fun r => if r.val<t.val then z r else y r)) := by
  classical
  letI : DecidableEq ℕ := fun a b => Classical.propDecidable (a=b)
  let e : Fin 9 × Fin 8 ≃ Fin 72 := finProdFinEquiv
  let h : EngineParams ≃ (Fin 72 → ℝ) := {
    toFun := fun x i => x (e.symm i).1 (e.symm i).2
    invFun := fun z r j => z (e (r,j))
    left_inv := by intro x; funext r j; simp
    right_inv := by intro z; funext i; simp }
  let endpoint (b : Bool) : EngineParams := if b then y else x
  have hg : ∀ b, EngineGeneric (endpoint b) := by intro b; cases b <;> assumption
  let mix (b : Bool) (t : Fin 10) (z : EngineParams) : EngineParams :=
    fun r => if r.val<t.val then z r else endpoint b r
  let sub (b : Bool) (t : Fin 10) (p : MvPolynomial (Fin 72) ℝ) : MvPolynomial (Fin 72) ℝ :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => if (e.symm i).1.val<t.val then MvPolynomial.X i
        else MvPolynomial.C (h (endpoint b) i)) p
  have heval : ∀ b t p z, MvPolynomial.eval (h z) (sub b t p)=
      MvPolynomial.eval (h (mix b t z)) p := by
    intro b t p z
    change ((MvPolynomial.eval (h z)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i => if (e.symm i).1.val<t.val then MvPolynomial.X i
          else MvPolynomial.C (h (endpoint b) i)))) p = _
    apply congrArg (fun f : MvPolynomial (Fin 72) ℝ →+* ℝ => f p)
    ext i <;> simp [mix,h,apply_ite]
    split_ifs <;> rfl
  obtain ⟨haug,hlin⟩ := Sierksma.engine_determinants_polynomial
  choose pa hpa using haug
  choose pl hpl using hlin
  have hpa' : ∀ s z, MvPolynomial.eval (h z) (pa s)=augmentedDet (EngineMap z) s :=
    fun s z => hpa s z
  have hpl' : ∀ s z, MvPolynomial.eval (h z) (pl s)=linearDet (EngineMap z) s :=
    fun s z => hpl s z
  let A := Σ j : Fin 3, ↥(EngineCone j).support
  let L := Σ a : A, ↥a.2.val
  let I := A ⊕ L
  let base : I → MvPolynomial (Fin 72) ℝ := fun i => match i with
    | Sum.inl a => pa a.2.val
    | Sum.inr l => pl (l.1.2.val.erase l.2.val)
  have hbase : ∀ b i, MvPolynomial.eval (h (endpoint b)) (base i) ≠ 0 := by
    intro b i
    cases i with
    | inl a =>
      change MvPolynomial.eval (h (endpoint b)) (pa a.2.val) ≠ 0
      rw [hpa']
      exact (hg b a.1 a.2.val a.2.property).2.1
    | inr l =>
      change MvPolynomial.eval (h (endpoint b)) (pl (l.1.2.val.erase l.2.val)) ≠ 0
      rw [hpl']
      exact (hg b l.1.1 l.1.2.val l.1.2.property).2.2 l.2.val l.2.property
  let J := Bool × Fin 10 × I
  let P (j : J) := sub j.1 j.2.1 (base j.2.2)
  have hP : ∀ j : J, P j ≠ 0 := by
    intro j
    have hh : MvPolynomial.eval (h (endpoint j.1)) (P j) ≠ 0 := by
      dsimp [P]
      rw [heval]
      have hm : mix j.1 j.2.1 (endpoint j.1)=endpoint j.1 := by
        funext r
        dsimp [mix]
        split_ifs <;> rfl
      rw [hm]
      exact hbase _ _
    intro hz
    rw [hz,map_zero] at hh
    exact hh rfl
  let Q : MvPolynomial (Fin 72) ℝ := ∏ j : J, P j
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hP j)
  obtain ⟨q,hq⟩ := (PLDegree.polynomial_nonzero_open_dense Q hQ).2.nonempty
  let z := h.symm q
  have hvals : ∀ j : J, MvPolynomial.eval (h z) (P j) ≠ 0 := by
    have hh : MvPolynomial.eval (h z) Q ≠ 0 := by simpa [z] using hq
    rw [show MvPolynomial.eval (h z) Q = ∏ j : J,
      MvPolynomial.eval (h z) (P j) by simp [Q]] at hh
    exact fun j => Finset.prod_ne_zero_iff.mp hh j (Finset.mem_univ j)
  have hall : ∀ b t, EngineGeneric (mix b t z) := by
    intro b t j s hs
    refine ⟨(hg b j s hs).1, ?_, ?_⟩
    · have hh := hvals (b,t,Sum.inl ⟨j,⟨s,hs⟩⟩)
      change MvPolynomial.eval (h z) (sub b t (pa s)) ≠ 0 at hh
      rwa [heval,hpa'] at hh
    · intro v hv
      have hh := hvals (b,t,Sum.inr ⟨⟨j,⟨s,hs⟩⟩,⟨v,hv⟩⟩)
      change MvPolynomial.eval (h z) (sub b t (pl (s.erase v))) ≠ 0 at hh
      rwa [heval,hpl'] at hh
  exact ⟨z,hall false,hall true⟩
