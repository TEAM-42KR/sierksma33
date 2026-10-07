import SierksmaLean.Theorems.Thm_Sierksma_FB_partOf_bij
import SierksmaLean.Theorems.Thm_Sierksma_FB_covOf_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col
import SierksmaLean.Theorems.Thm_Sierksma_signed_covers
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma Sierksma.FB
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem proof_Sierksma_FB_index_transfer (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Sierksma.Universe 3) (hy : Sierksma.SignedSystem y) :
    (Sierksma.FB.idxSupp y).card = ((Sierksma.Universe 3).filter (fun Q => y Q ≠ 0)).card ∧
      (∀ i ∈ Sierksma.FB.idxSupp y, i < 1855) ∧
      Sierksma.FB.signedIdx (Sierksma.FB.idxSupp y) ∧ Sierksma.FB.coversIdx (Sierksma.FB.idxSupp y) := by
  classical
  let I := idxSupp y
  let U := (Universe 3).filter (fun Q => y Q ≠ 0)
  have hir (i : ℕ) (hi : i ∈ I) : i < 1855 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hinz (i : ℕ) (hi : i ∈ I) : y (partOf i) ≠ 0 :=
    (Finset.mem_filter.mp hi).2
  have hinj : Set.InjOn partOf (↑I : Set ℕ) := by
    intro i hi j hj he
    exact Sierksma.FB.partOf_bij.1 i (hir i hi) j (hir j hj) he
  have hiU : I.image partOf = U := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      refine Finset.mem_filter.mpr ⟨?_, hinz i hi⟩
      rw [← Sierksma.FB.partOf_bij.2.1]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (hir i hi), rfl⟩
    · intro hQ
      have hQu := (Finset.mem_filter.mp hQ).1
      have hQnz := (Finset.mem_filter.mp hQ).2
      rw [← Sierksma.FB.partOf_bij.2.1] at hQu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQu
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hQnz⟩, rfl⟩
  have hU3 : U ⊆ ThreePartitions 9 := by
    intro Q hQ
    have hu : Q ∈ Universe 3 := (Finset.mem_filter.mp hQ).1
    have hp : IsPartition Q 3 := (Finset.mem_filter.mp hu).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  have hsum (w : Common.Partition 9 → ZMod 3) :
      ∑ i ∈ I, y (partOf i) * w (partOf i) =
        ∑ Q ∈ ThreePartitions 9, y Q * w Q := by
    calc
      _ = ∑ Q ∈ U, y Q * w Q := by
        rw [← hiU]
        exact (Finset.sum_image (f := fun Q => y Q * w Q) hinj).symm
      _ = _ := Finset.sum_subset hU3 (by
        intro Q hQ hnot
        have hz : y Q = 0 := by
          by_contra hn
          exact hnot (Finset.mem_filter.mpr ⟨hsupp Q hn, hn⟩)
        simp [hz])
  have hdiff (i : ℕ) (hi : i < 1855) (u v : Fin 9) :
      EdgeDiff (partOf i) (u, v) = ((dI i u.val v.val : ℕ) : ZMod 3) := by
    have hcu := (Sierksma.FB.tab_col.1 i hi).2.1 u.val u.isLt
    have hle : colOf i u.val ≤ colOf i v.val + 3 := by omega
    rw [EdgeDiff, Sierksma.FB.partOf_bij.2.2 i hi v,
      Sierksma.FB.partOf_bij.2.2 i hi u]
    change (colOf i v.val : ZMod 3) - (colOf i u.val : ZMod 3) =
      (((colOf i v.val + 3 - colOf i u.val) % 3 : ℕ) : ZMod 3)
    rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add]
    norm_num
    exact ZMod.natCast_self 3
  refine ⟨?_, hir, ?_, ?_⟩
  · change I.card = U.card
    rw [← hiU]
    exact (Finset.card_image_iff.mpr hinj).symm
  · refine ⟨fun i => y (partOf i), hinz, ?_, ?_⟩
    · have hh := hsum (fun _ => 1)
      simpa only [mul_one, hy.1] using hh
    · intro u v u' v' huv hu'v' hv hv' huu' huv' hvu' hvv'
      let uf : Fin 9 := ⟨u, by omega⟩
      let vf : Fin 9 := ⟨v, hv⟩
      let uf' : Fin 9 := ⟨u', by omega⟩
      let vf' : Fin 9 := ⟨v', hv'⟩
      have hd : Disjoint (Endpoints (uf, vf)) (Endpoints (uf', vf')) := by
        simp [Endpoints, Finset.disjoint_left, uf, vf, uf', vf', huu', huv', hvu', hvv']
      have heq : (∑ i ∈ I, y (partOf i) * ((dI i u v : ℕ) : ZMod 3) *
          ((dI i u' v' : ℕ) : ZMod 3)) =
          ∑ Q ∈ ThreePartitions 9, y Q * EdgeDiff Q (uf, vf) * EdgeDiff Q (uf', vf') := by
        calc
          _ = ∑ i ∈ I, y (partOf i) *
              (EdgeDiff (partOf i) (uf, vf) * EdgeDiff (partOf i) (uf', vf')) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hdiff i (hir i hi) uf vf, hdiff i (hir i hi) uf' vf']
            exact mul_assoc _ _ _
          _ = _ := by simpa only [mul_assoc] using
            (hsum (fun Q => EdgeDiff Q (uf, vf) * EdgeDiff Q (uf', vf')))
      rw [heq]
      exact hy.2.1 (uf, vf) (uf', vf') huv hu'v' hd
  · intro g hg
    obtain ⟨Q, hQ3, hQnz, hcov⟩ := Sierksma.signed_covers y hy (constraintOf g)
      (Sierksma.FB.covOf_spec.1 g hg)
    have hu := hsupp Q hQnz
    rw [← Sierksma.FB.partOf_bij.2.1] at hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hi' := Finset.mem_range.mp hi
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hQnz⟩,
      (Sierksma.FB.covOf_spec.2.2 g hg i hi').mpr hcov⟩
