import Mathlib
set_option autoImplicit false

open Set Filter Topology

theorem proof_PLDegree_polynomial_nonzero_open_dense {k : ℕ}
    (p : MvPolynomial (Fin k) ℝ) (hp : p ≠ 0) :
    IsOpen {x : Fin k → ℝ | MvPolynomial.eval x p ≠ 0} ∧
    Dense {x : Fin k → ℝ | MvPolynomial.eval x p ≠ 0} := by
  have ha : AnalyticOnNhd ℝ (fun x : Fin k → ℝ => MvPolynomial.eval x p) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial p
  have hc : Continuous (fun x : Fin k → ℝ => MvPolynomial.eval x p) :=
    continuousOn_univ.mp ha.continuousOn
  refine ⟨isOpen_ne.preimage hc, dense_iff_inter_open.mpr ?_⟩
  intro U hU hUne
  obtain ⟨z, hz⟩ := hUne
  by_contra hnone
  have hzero : ∀ x ∈ U, MvPolynomial.eval x p = 0 := by
    intro x hx
    by_contra hne
    exact hnone ⟨x, hx, hne⟩
  have hevent : (fun x : Fin k → ℝ => MvPolynomial.eval x p) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hU.mem_nhds hz] with x hx
    exact hzero x hx
  have heq : (fun x : Fin k → ℝ => MvPolynomial.eval x p) = 0 :=
    ha.eq_of_eventuallyEq analyticOnNhd_const hevent
  apply hp
  apply MvPolynomial.funext
  intro x
  have hh := congrFun heq x
  simpa using hh
