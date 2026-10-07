import SierksmaLean.Definitions.Def_PLDegree_Chain
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace PLDegree

def AffineRayHit {n : ℕ} (a b : Fin (n+1) → ℝ) (i : Fin (n+1)) : Prop :=
  ∃ t : ℝ, 0<t ∧ a i+t*b i=0 ∧ ∀ j, 0 ≤ a j+t*b j

def AffineSlopeSum {n : ℕ} (a b : Fin (n+1) → ℝ) : ℤ :=
  ∑ i, if AffineRayHit a b i then (SignType.sign (b i) : ℤ) else 0

def PositiveAtZero {n : ℕ} (a : Fin (n+1) → ℝ) : Prop := ∀ i, 0<a i

def IntervalGeneric {n : ℕ} (a b : Fin (n+1) → ℝ) : Prop :=
  (∀ i, b i ≠ 0) ∧
  ((∀ i, 0 ≤ a i) → PositiveAtZero a) ∧
  (∀ t : ℝ, 0<t → (∀ k, 0 ≤ a k+t*b k) →
    ∀ i j : Fin (n+1), i ≠ j → ¬ (a i+t*b i=0 ∧ a j+t*b j=0))

end PLDegree
