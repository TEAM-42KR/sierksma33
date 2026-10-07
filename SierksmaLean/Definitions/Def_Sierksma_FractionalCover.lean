import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Common
namespace Sierksma
attribute [local instance] Classical.propDecidable
def PrimalFeasible (d : ℕ) (y : Common.Partition (N d) → ℝ) : Prop :=
 (∀ Q ∈ Universe d, 0 ≤ y Q) ∧ ∀ g, ValidConstraint d g → 1 ≤ ∑ Q ∈ Universe d, if Covers Q g then y Q else 0
def DualFeasible (d : ℕ) (w : PairConstraint (N d) → ℝ) : Prop :=
 (∀ g ∈ Constraints d, 0 ≤ w g) ∧ ∀ Q ∈ Universe d, (∑ g ∈ Constraints d, if Covers Q g then w g else 0) ≤ 1
def FractionalCover (d : ℕ) : ℝ := sInf {v | ∃ y, PrimalFeasible d y ∧ v = ∑ Q ∈ Universe d, y Q}
def DualValue (d : ℕ) : ℝ := sSup {v | ∃ w, DualFeasible d w ∧ v = ∑ g ∈ Constraints d, w g}
def TailPoly (m k : ℕ) : Polynomial ℕ :=
 (Polynomial.C 2 + Polynomial.X) * (Polynomial.C 2 + Polynomial.C 4 * Polynomial.X)^k *
 (Polynomial.C 3 + Polynomial.C 2 * Polynomial.X + Polynomial.X^2)^(m-k)
def BTail (m : ℕ) : ℕ := (Finset.range (m+1)).sup (fun k =>
 ∑ j ∈ Finset.range (2*m+2), if m+1 ≤ j then (TailPoly m k).coeff j else 0)
def Primal3 (Q : Common.Partition 9) : ℝ :=
 if TypeIs Q ({1,4,4} : Multiset ℕ) then 1/648 else if TypeIs Q ({3,3,3} : Multiset ℕ) then 1/108 else 0
def Dual3 (g : PairConstraint 9) : ℝ :=
 if (∀ e ∈ g.matching, g.twists e ≠ 0) then 1/7776 else if (∀ e ∈ g.matching, g.twists e = 0) then 7/5832 else 0
end Sierksma
