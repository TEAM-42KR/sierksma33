import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open Sierksma.FB

theorem proof_Sierksma_FB_validPerm_equiv (p : ℕ) (hp : validPerm p = true) : ∃ π : Equiv.Perm (Fin 9), ∀ v : Fin 9, (π v).val = pAt p v.val := by
  classical
  have hp0 : (List.range 9).all (fun v => Nat.blt (pAt p v) 9) = true :=
    (Bool.and_eq_true_iff.mp hp).1
  have hp1 : (List.range 9).all (fun v => (List.range 9).all
      (fun w => Nat.beq v w || !(Nat.beq (pAt p v) (pAt p w)))) = true :=
    (Bool.and_eq_true_iff.mp hp).2
  have hlt (v : Fin 9) : pAt p v.val < 9 := by
    have hh := (List.all_eq_true.mp hp0) v.val (List.mem_range.mpr v.isLt)
    simpa using hh
  let f : Fin 9 → Fin 9 := fun v => ⟨pAt p v.val, hlt v⟩
  have hf : Function.Injective f := by
    intro v w h
    have hh := (List.all_eq_true.mp
      ((List.all_eq_true.mp hp1) v.val (List.mem_range.mpr v.isLt))) w.val
      (List.mem_range.mpr w.isLt)
    have he : pAt p v.val = pAt p w.val := congrArg Fin.val h
    have hv : v.val = w.val := by simpa [he] using hh
    exact Fin.ext hv
  let π : Equiv.Perm (Fin 9) := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  have hπ (v : Fin 9) : (π v).val = pAt p v.val := rfl
  exact ⟨π,hπ⟩
