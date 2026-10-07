import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_rqlift_determinant_eq_triple
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem proof_Sierksma_g4_sorted_triples_suffice (P : RQConfig)
    (h : ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9,
      StrictMono t → StrictMono t' →
      Disjoint (Endpoints e) (Finset.univ.image t) →
      Disjoint (Endpoints e) (Finset.univ.image t') →
      Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly P e t t' ≠ 0) :
    ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9,
      Function.Injective t → Function.Injective t' →
      Disjoint (Endpoints e) (Finset.univ.image t) →
      Disjoint (Endpoints e) (Finset.univ.image t') →
      Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly P e t t' ≠ 0 := by
  classical
  let D : Fin 9 → (Fin 3 → Fin 9) → ℚ := fun u s =>
    Matrix.det (Matrix.of (fun i j : Fin 4 => RQLift P (![u,s 0,s 1,s 2] i) j.val))
  have h3 (s : Fin 3 → Fin 9) (q : Fin 3 → ℚ) : RQTripleDet P s q =
      (P (s 1) 0-P (s 0) 0)*(P (s 2) 1-P (s 0) 1)*q 2 -
      (P (s 1) 0-P (s 0) 0)*(P (s 2) 2-P (s 0) 2)*q 1 -
      (P (s 1) 1-P (s 0) 1)*(P (s 2) 0-P (s 0) 0)*q 2 +
      (P (s 1) 1-P (s 0) 1)*(P (s 2) 2-P (s 0) 2)*q 0 +
      (P (s 1) 2-P (s 0) 2)*(P (s 2) 0-P (s 0) 0)*q 1 -
      (P (s 1) 2-P (s 0) 2)*(P (s 2) 1-P (s 0) 1)*q 0 := by
    change Matrix.det (Matrix.of ![P (s 1)-P (s 0), P (s 2)-P (s 0), q]) = _
    rw [Matrix.det_fin_three]
    simp [Matrix.of_apply, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
  have hDu (u : Fin 9) (s : Fin 3 → Fin 9) :
      D u s = RQTripleDet P s (P u-P (s 0)) := Sierksma.rqlift_determinant_eq_triple P u s
  have hDv (u v : Fin 9) (s : Fin 3 → Fin 9) :
      RQTripleDet P s (P v-P u) = D v s-D u s := by
    rw [hDu, hDu]
    simp only [h3, Pi.sub_apply]
    ring
  have hQ (e : Edge 9) (s s' : Fin 3 → Fin 9) :
      RQQPoly P e s s' = D e.2 s * D e.1 s' - D e.2 s' * D e.1 s := by
    unfold RQQPoly
    rw [hDv e.1 e.2 s, hDv e.1 e.2 s', ← hDu e.1 s', ← hDu e.1 s]
    ring
  have hsort (s : Fin 3 → Fin 9) (hs : Function.Injective s) :
      ∃ b : Fin 3 → Fin 9, ∃ p : Equiv.Perm (Fin 3),
        StrictMono b ∧ (∀ i, b (p i)=s i) ∧ Finset.univ.image b=Finset.univ.image s := by
    let S := Finset.univ.image s
    have hS : S.card=3 := by simpa [S] using Finset.card_image_of_injective Finset.univ hs
    let e : Fin 3 ≃o S := S.orderIsoOfFin hS
    let b : Fin 3 → Fin 9 := fun i => (e i).val
    let f : Fin 3 → S := fun i => ⟨s i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        exact hs (congrArg (fun x : S => x.val) hij)
      · intro x
        obtain ⟨i, hi, he⟩ := Finset.mem_image.mp x.property
        exact ⟨i, Subtype.ext he⟩
    let p : Equiv.Perm (Fin 3) := (Equiv.ofBijective f hf).trans e.toEquiv.symm
    refine ⟨b,p,(S.orderEmbOfFin hS).strictMono, ?_, ?_⟩
    · intro i
      simp [p,b,f]
    · exact S.image_orderEmbOfFin_univ hS
  have hdegree (s b : Fin 3 → Fin 9) (p : Equiv.Perm (Fin 3))
      (hp : ∀ i, b (p i)=s i) :
      ∃ a : ℚ, a ≠ 0 ∧ ∀ u, D u s = a * D u b := by
    let rho : Equiv.Perm (Fin 4) := Equiv.Perm.decomposeFin.symm (0,p)
    let a : ℚ := (((Equiv.Perm.sign rho : ℤˣ) : ℤ) : ℚ)
    have hvec (u : Fin 9) (q : Fin 3 → Fin 9) (j : Fin 3) :
        (![u,q 0,q 1,q 2] : Fin 4 → Fin 9) j.succ = q j := by fin_cases j <;> rfl
    have hr (u : Fin 9) (i : Fin 4) :
        (![u,b 0,b 1,b 2] : Fin 4 → Fin 9) (rho i) = ![u,s 0,s 1,s 2] i := by
      refine Fin.cases ?_ ?_ i
      · simp only [rho, Equiv.Perm.decomposeFin_symm_apply_zero]
        rfl
      · intro j
        simp only [rho, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
          Equiv.refl_apply, hvec, hp]
    refine ⟨a, ?_, ?_⟩
    · change (((Equiv.Perm.sign rho : ℤˣ) : ℤ) : ℚ) ≠ 0
      exact_mod_cast (Units.ne_zero (Equiv.Perm.sign rho))
    · intro u
      let M : Matrix (Fin 4) (Fin 4) ℚ := fun i j => RQLift P (![u,b 0,b 1,b 2] i) j.val
      have hm : Matrix.of (fun i j : Fin 4 => RQLift P (![u,s 0,s 1,s 2] i) j.val) =
          Matrix.of (fun i => M (rho i)) := by
        ext i j
        change RQLift P (![u,s 0,s 1,s 2] i) j.val =
          RQLift P (![u,b 0,b 1,b 2] (rho i)) j.val
        rw [hr]
      change Matrix.det (Matrix.of (fun i j : Fin 4 => RQLift P (![u,s 0,s 1,s 2] i) j.val)) = a * M.det
      rw [hm]
      have hc (z : ℚ) : (Equiv.Perm.sign rho) • z = a * z := by
        rw [Units.smul_def, zsmul_eq_mul]
      exact (Matrix.det_permute rho M).trans (hc M.det)
  intro e he t t' ht ht' het het' htt'
  obtain ⟨b,p,hb,hp,hbi⟩ := hsort t ht
  obtain ⟨b',p',hb',hp',hbi'⟩ := hsort t' ht'
  have hroot : RQQPoly P e b b' ≠ 0 := h e he b b' hb hb'
    (by rwa [hbi]) (by rwa [hbi']) (by rwa [hbi,hbi'])
  obtain ⟨a,ha,hDa⟩ := hdegree t b p hp
  obtain ⟨a',ha',hDa'⟩ := hdegree t' b' p' hp'
  have hrel : RQQPoly P e t t' = (a*a') * RQQPoly P e b b' := by
    rw [hQ,hQ]
    rw [hDa,hDa,hDa',hDa']
    ring
  rw [hrel]
  exact mul_ne_zero (mul_ne_zero ha ha') hroot
