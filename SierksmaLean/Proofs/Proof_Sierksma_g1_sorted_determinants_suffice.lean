import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma
open scoped BigOperators

theorem proof_Sierksma_g1_sorted_determinants_suffice (P : RQConfig)
    (h : ∀ a : Fin 4 → Fin 9, StrictMono a →
      Matrix.det (fun i j : Fin 4 => RQLift P (a i) j.val) ≠ 0) :
    ∀ a : Fin 4 → Fin 9, Function.Injective a →
      Matrix.det (fun i j : Fin 4 => RQLift P (a i) j.val) ≠ 0 := by
  classical
  intro a ha
  let S := Finset.univ.image a
  have hS : S.card = 4 := by simpa [S] using Finset.card_image_of_injective Finset.univ ha
  let e : Fin 4 ≃o S := S.orderIsoOfFin hS
  let b : Fin 4 → Fin 9 := fun i => (e i).val
  have hb : StrictMono b := (S.orderEmbOfFin hS).strictMono
  let f : Fin 4 → S := fun i => ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact ha (congrArg (fun x : S => x.val) hij)
    · intro x
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp x.property
      exact ⟨i, Subtype.ext he⟩
  let p : Equiv.Perm (Fin 4) := (Equiv.ofBijective f hf).trans e.toEquiv.symm
  have hp : ∀ i, b (p i) = a i := by
    intro i
    simp [p, b, f]
  let M : Matrix (Fin 4) (Fin 4) ℚ := fun i j => RQLift P (b i) j.val
  have hM : M.det ≠ 0 := h b hb
  have he : Matrix.det (Matrix.of (fun i j : Fin 4 => RQLift P (a i) j.val)) =
      (Equiv.Perm.sign p) • M.det := by
    calc
      _ = Matrix.det (Matrix.of (fun i => M (p i))) := by
        congr 1
        ext i j
        simp [M, hp]
      _ = (Equiv.Perm.sign p) • M.det := Matrix.det_permute p M
  change Matrix.det (Matrix.of (fun i j : Fin 4 => RQLift P (a i) j.val)) ≠ 0
  rw [he, Units.smul_def, zsmul_eq_mul]
  have hs : (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (Units.ne_zero (Equiv.Perm.sign p))
  exact mul_ne_zero hs hM
