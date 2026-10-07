import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Common
namespace Sierksma
def TwistFace (d : ℕ) (g : PairConstraint (N d)) (s : Finset (Fin (N d) × ZMod 3)) : Prop :=
 (∀ v a b, (v,a) ∈ s → (v,b) ∈ s → a=b) ∧
 ∀ e ∈ g.matching, ∀ a b, (e.1,a) ∈ s → (e.2,b) ∈ s → b-a ≠ g.twists e
def FaceDimension (d : ℕ) (g : PairConstraint (N d)) : ℕ := by
 classical
 exact (Finset.univ.filter (TwistFace d g)).sup (fun s => s.card-1)
def RealizationCondition (d : ℕ) (g : PairConstraint (N d)) (w : Fin (N d) × ZMod 3 → ℝ) : Prop :=
 (∀ x, 0 ≤ w x) ∧ (∑ x, w x = 1) ∧
 (∀ v a b, 0 < w (v,a) → 0 < w (v,b) → a=b) ∧
 ∀ e ∈ g.matching, ∀ a b, 0 < w (e.1,a) → 0 < w (e.2,b) → b-a ≠ g.twists e
def TwistedRealization (d : ℕ) (g : PairConstraint (N d)) :=
 {w : Fin (N d) × ZMod 3 → ℝ // RealizationCondition d g w}
def NConnected (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
 Nonempty X ∧ ∀ k : ℕ, k ≤ n →
 ∀ f : C(↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (k+1))) 1), X),
 ∃ g : C(EuclideanSpace ℝ (Fin (k+1)), X), ∀ x, g x.val = f x
def ShiftWeights (w : Fin (N 0) × ZMod 3 → ℝ) (a : ZMod 3) : Fin (N 0) × ZMod 3 → ℝ :=
 fun x => w (x.1,x.2-a)
def PositiveCoincidence (d : ℕ) (P : Config (N d) d) (g : PairConstraint (N d)) : Prop :=
 ∃ s : Finset (Fin (N d) × ZMod 3), TwistFace d g s ∧
 (∀ j : ZMod 3, ∃ v, (v,j) ∈ s) ∧ ∃ μ : Fin (N d) × ZMod 3 → ℝ,
 (∀ x ∈ s, 0 < μ x) ∧ (∀ j : ZMod 3, (∑ v, if (v,j) ∈ s then μ (v,j) else 0) = 1) ∧
 ∃ z : Fin d → ℝ, ∀ j : ZMod 3, (∑ v, if (v,j) ∈ s then μ (v,j) • P v else 0) = z
end Sierksma
