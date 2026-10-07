import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_g1_polynomial_affine_gp
set_option autoImplicit false
open Common Sierksma Set
open scoped BigOperators

theorem proof_Sierksma_generic_locus_strong_gp : ∀ P ∈ GenericLocus, StrongGP P := by
  classical
  intro P hP
  refine ⟨Sierksma.g1_polynomial_affine_gp P hP.1, ?_⟩
  have henumerate (T : Finset (Fin 9)) (hT : T.card = 3) :
      ∃ t : Fin 3 → Fin 9, Function.Injective t ∧ Finset.univ.image t = T := by
    let e : T ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hT)
    let t : Fin 3 → Fin 9 := fun i => (e.symm i).val
    refine ⟨t, Subtype.val_injective.comp e.symm.injective, ?_⟩
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (e.symm i).property
    · intro hv
      refine Finset.mem_image.mpr ⟨e ⟨v, hv⟩, Finset.mem_univ _, ?_⟩
      simp [t]
  have hcalc (t : Fin 3 → Fin 9) (q : Fin 3 → ℝ) : TripleDet P t q =
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 1-P (t 0) 1)*q 2 -
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 2-P (t 0) 2)*q 1 -
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 0-P (t 0) 0)*q 2 +
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 2-P (t 0) 2)*q 0 +
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 0-P (t 0) 0)*q 1 -
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 1-P (t 0) 1)*q 0 := by
    change Matrix.det (Matrix.of ![P (t 1)-P (t 0), P (t 2)-P (t 0), q]) = _
    rw [Matrix.det_fin_three]
    simp [Matrix.of_apply, Matrix.vecTail, Matrix.vecHead, Pi.sub_apply]
  have hplane (t : Fin 3 → Fin 9) (z : Fin 3 → ℝ)
      (hz : z ∈ affineSpan ℝ (range (fun i => P (t i)))) :
      TripleDet P t (z-P (t 0)) = 0 := by
    let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := {
      toFun := fun q => TripleDet P t q
      map_add' := by
        intro q r
        simp only [hcalc, Pi.add_apply]
        ring
      map_smul' := by
        intro c q
        simp only [hcalc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    let F : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ :=
      L.toAffineMap - AffineMap.const ℝ (Fin 3 → ℝ) (L (P (t 0)))
    have hbase : ∀ i : Fin 3, F (P (t i)) = 0 := by
      intro i
      change L (P (t i)) - L (P (t 0)) = 0
      rw [← L.map_sub]
      change TripleDet P t (P (t i)-P (t 0)) = 0
      rw [hcalc]
      fin_cases i <;> simp [Pi.sub_apply] <;> ring
    have he : (range (fun i => P (t i))).EqOn F (AffineMap.const ℝ (Fin 3 → ℝ) 0) := by
      rintro x ⟨i, rfl⟩
      exact hbase i
    have hz' := AffineMap.eqOn_affineSpan he hz
    change L z - L (P (t 0)) = 0 at hz'
    rw [← L.map_sub] at hz'
    exact hz'
  intro E T T' hE hT hT' hET hET' hTT'
  rintro ⟨z, hzE, hzT, hzT'⟩
  have hep : ∃ u v : Fin 9, u < v ∧ E = {u,v} := by
    obtain ⟨u,v,hne,hEq⟩ := Finset.card_eq_two.mp hE
    rcases lt_or_gt_of_ne hne with huv | hvu
    · exact ⟨u,v,huv,hEq⟩
    · exact ⟨v,u,hvu,by simpa [Finset.pair_comm] using hEq⟩
  obtain ⟨u,v,huv,hEq⟩ := hep
  obtain ⟨t, ht, hti⟩ := henumerate T hT
  obtain ⟨t', ht', hti'⟩ := henumerate T' hT'
  let e : Edge 9 := (u,v)
  have hETt : Disjoint (Endpoints e) (Finset.univ.image t) := by
    simpa [e, Endpoints, hEq, hti] using hET
  have hETt' : Disjoint (Endpoints e) (Finset.univ.image t') := by
    simpa [e, Endpoints, hEq, hti'] using hET'
  have hTtt' : Disjoint (Finset.univ.image t) (Finset.univ.image t') := by
    simpa [hti,hti'] using hTT'
  have hQ : QPoly P e t t' ≠ 0 := hP.2.1 e huv t t' ht ht' hETt hETt' hTtt'
  have hTset (s : Fin 3 → Fin 9) (S : Finset (Fin 9)) (hi : Finset.univ.image s = S) :
      range (fun i => P (s i)) = P '' (S : Set (Fin 9)) := by
    rw [← hi]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i, rfl⟩
  have hzE' : z ∈ affineSpan ℝ ({P u,P v} : Set (Fin 3 → ℝ)) := by
    simpa only [hEq, Finset.coe_pair, Set.image_insert_eq, Set.image_singleton] using hzE
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp hzE'
  have hroot (s : Fin 3 → Fin 9)
      (hz : z ∈ affineSpan ℝ (range (fun i => P (s i)))) :
      r * TripleDet P s (P v-P u) + TripleDet P s (P u-P (s 0)) = 0 := by
    have hp := hplane s z hz
    have he : z-P (s 0) = r • (P v-P u) + (P u-P (s 0)) := by
      rw [← hr, AffineMap.lineMap_apply_module']
      abel
    rw [he] at hp
    simp only [hcalc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp ⊢
    linear_combination hp
  have hrT := hroot t (by rwa [hTset t T hti])
  have hrT' := hroot t' (by rwa [hTset t' T' hti'])
  apply hQ
  change TripleDet P t (P v-P u) * TripleDet P t' (P u-P (t' 0)) -
      TripleDet P t' (P v-P u) * TripleDet P t (P u-P (t 0)) = 0
  linear_combination (TripleDet P t (P v-P u))*hrT' -
    (TripleDet P t' (P v-P u))*hrT
