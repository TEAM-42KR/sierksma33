import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false
open Sierksma.FB

theorem proof_Sierksma_FB_Kbuild_spec (P : ℕ → Bool) (x : ℕ) :
    Nat.testBit (Kbuild P) x = (Nat.blt x 1855 && P x) := by
  have hrec (n : ℕ) : ∀ x : ℕ,
      Nat.testBit
        (Nat.rec (motive := fun _ => ℕ) 0
          (fun j acc => Nat.lor acc (cond (P j) (Nat.shiftLeft 1 j) 0)) n) x =
        (decide (x < n) && P x) := by
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      change Nat.testBit (Nat.lor _ (cond (P n) (Nat.shiftLeft 1 n) 0)) x = _
      rw [Nat.lor_eq, Nat.testBit_or, ih]
      by_cases hx : x = n
      · subst x
        cases hp : P n <;>
          simp [hp, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
      · have hlt : x < n + 1 ↔ x < n := by omega
        cases hp : P n <;>
          simp [hp, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
            hx, Ne.symm hx, hlt]
  have hb : Nat.blt x 1855 = decide (x < 1855) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Nat.blt_eq, decide_eq_true_eq]
  rw [hb]
  exact hrec 1855 x
