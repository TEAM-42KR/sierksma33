import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
theorem proof_Sierksma_respects_two_orientations {n : ℕ} (Q : Common.Partition n) (c d : Fin n → ZMod 3) (hc : Sierksma.Respects Q c) (hd : Sierksma.Respects Q d) (u v : Fin n) (hne : c u ≠ c v) : (∀ x y, d y - d x = c y - c x) ∨ (∀ x y, d y - d x = -(c y - c x)) := by
  have scalar : ∀ a b c d x y : ZMod 3, a ≠ b → c ≠ d → (x = a ↔ y = c) → (x = b ↔ y = d) → (d-c)*(x-a) = (b-a)*(y-c) := by decide
  have kernel : ∀ x y, c x = c y ↔ d x = d y := fun x y => (hc x y).trans (hd x y).symm
  have hdne : d u ≠ d v := fun h => hne ((kernel u v).mpr h)
  let a : ZMod 3 := (d v - d u) / (c v - c u)
  have hcu : c v - c u ≠ 0 := sub_ne_zero.mpr hne.symm
  have hdu : d v - d u ≠ 0 := sub_ne_zero.mpr hdne.symm
  have ha : a ≠ 0 := div_ne_zero hdu hcu
  have hx : ∀ x, d x - d u = a * (c x - c u) := by
    intro x
    have h := scalar (c u) (c v) (d u) (d v) (c x) (d x) hne hdne (kernel x u) (kernel x v)
    dsimp [a]
    field_simp
    linear_combination -h
  have hs : a = 1 ∨ a = -1 := by
    revert ha
    generalize a = z
    decide +revert
  rcases hs with hs | hs
  · left
    intro x y
    have h1 := hx x
    have h2 := hx y
    rw [hs, one_mul] at h1 h2
    linear_combination h2-h1
  · right
    intro x y
    have h1 := hx x
    have h2 := hx y
    rw [hs, neg_one_mul] at h1 h2
    linear_combination h2-h1
