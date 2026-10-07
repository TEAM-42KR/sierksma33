import SierksmaLean.Theorems.Thm_Sierksma_engine_determinants_polynomial
import SierksmaLean.Theorems.Thm_PLDegree_polynomial_nonzero_open_dense
set_option autoImplicit false
open PLDegree Sierksma
open scoped BigOperators

theorem proof_Sierksma_engine_generic_dense_of_witness (w : EngineParams) (hw : EngineGeneric w) :
    Dense {x : EngineParams | EngineGeneric x} := by
  classical
  letI : DecidableEq ℕ := fun a b => Classical.propDecidable (a=b)
  let e : Fin 9 × Fin 8 ≃ Fin 72 := finProdFinEquiv
  let h : EngineParams ≃ₜ (Fin 72 → ℝ) := {
    toEquiv := {
      toFun := fun x i => x (e.symm i).1 (e.symm i).2
      invFun := fun z r j => z (e (r,j))
      left_inv := by intro x; funext r j; simp
      right_inv := by intro z; funext i; simp }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  obtain ⟨haug,hlin⟩ := Sierksma.engine_determinants_polynomial
  choose pa hpa using haug
  choose pl hpl using hlin
  have hpa' : ∀ s x, MvPolynomial.eval (h x) (pa s)=augmentedDet (EngineMap x) s :=
    fun s x => hpa s x
  have hpl' : ∀ s x, MvPolynomial.eval (h x) (pl s)=linearDet (EngineMap x) s :=
    fun s x => hpl s x
  let A := Σ j : Fin 3, ↥(EngineCone j).support
  let L := Σ a : A, ↥a.2.val
  let I := A ⊕ L
  let P : I → MvPolynomial (Fin 72) ℝ := fun i => match i with
    | Sum.inl a => pa a.2.val
    | Sum.inr l => pl (l.1.2.val.erase l.2.val)
  have hnonzero : ∀ i : I, P i ≠ 0 := by
    intro i
    have heval : MvPolynomial.eval (h w) (P i) ≠ 0 := by
      cases i with
      | inl a =>
        change MvPolynomial.eval (h w) (pa a.2.val) ≠ 0
        rw [hpa']
        exact (hw a.1 a.2.val a.2.property).2.1
      | inr l =>
        change MvPolynomial.eval (h w) (pl (l.1.2.val.erase l.2.val)) ≠ 0
        rw [hpl']
        exact (hw l.1.1 l.1.2.val l.1.2.property).2.2 l.2.val l.2.property
    intro hz
    rw [hz, map_zero] at heval
    exact heval rfl
  let Q : MvPolynomial (Fin 72) ℝ := ∏ i : I, P i
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hnonzero i)
  have hd : Dense (h ⁻¹' {z | MvPolynomial.eval z Q ≠ 0}) :=
    (PLDegree.polynomial_nonzero_open_dense Q hQ).2.preimage h.isOpenMap
  apply hd.mono
  intro x hx
  have hh : ∀ i : I, MvPolynomial.eval (h x) (P i) ≠ 0 := by
    change MvPolynomial.eval (h x) Q ≠ 0 at hx
    rw [show MvPolynomial.eval (h x) Q = ∏ i : I,
        MvPolynomial.eval (h x) (P i) by simp [Q]] at hx
    exact fun i => Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)
  intro j s hs
  refine ⟨(hw j s hs).1, ?_, ?_⟩
  · have hh' := hh (Sum.inl ⟨j,⟨s,hs⟩⟩)
    change MvPolynomial.eval (h x) (pa s) ≠ 0 at hh'
    rwa [hpa'] at hh'
  · intro v hv
    have hh' := hh (Sum.inr ⟨⟨j,⟨s,hs⟩⟩,⟨v,hv⟩⟩)
    change MvPolynomial.eval (h x) (pl (s.erase v)) ≠ 0 at hh'
    rwa [hpl'] at hh'
