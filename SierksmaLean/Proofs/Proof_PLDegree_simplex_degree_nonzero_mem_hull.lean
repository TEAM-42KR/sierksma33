import SierksmaLean.Definitions.Def_PLDegree_Chain
set_option autoImplicit false
open PLDegree
open scoped BigOperators

theorem proof_PLDegree_simplex_degree_nonzero_mem_hull {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (h : simplexDegree F s ≠ 0) :
    (0 : Fin n → ℝ) ∈ hull F s := by
  classical
  unfold simplexDegree at h
  split_ifs at h with hs hm
  · let w := barycentric F s hs
    have heq : Matrix.vecMul w (augmentedMatrix F s hs) = originRow n := by
      dsimp [w, barycentric]
      rw [Matrix.vecMul_vecMul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hm.1), Matrix.vecMul_one]
    have hsum : ∑ i, w i = 1 := by
      have hh := congrFun heq (Fin.last n)
      simpa [Matrix.vecMul, dotProduct, augmentedMatrix, augment, originRow] using hh
    have hz : ∑ i, w i • F (s.orderEmbOfFin hs i) = (0 : Fin n → ℝ) := by
      funext k
      have hh := congrFun heq k.castSucc
      simpa [Matrix.vecMul, dotProduct, augmentedMatrix, augment, originRow,
        k.isLt, Fin.castSucc_ne_last, Finset.sum_apply, Pi.smul_apply] using hh
    apply mem_convexHull_of_exists_fintype w (fun i => F (s.orderEmbOfFin hs i))
      (fun i => (hm.2 i).le) hsum _ hz
    intro i
    exact Set.mem_image_of_mem _ (s.orderEmbOfFin_mem hs i)
  · exact (h rfl).elim
  · exact (h rfl).elim
