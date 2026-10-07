import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Common
namespace Sierksma

def CanonColour {n : ℕ} (Q : Common.Partition n) (v : Fin n) : ZMod 3 :=
  ((Finset.univ.filter (fun u : Fin n =>
      (∀ w : Fin n, w < u → ¬ ∃ A ∈ Q, w ∈ A ∧ u ∈ A) ∧
        ∀ w : Fin n, (∃ A ∈ Q, w ∈ A ∧ v ∈ A) → u < w)).card : ZMod 3)

def EdgeDiff {n : ℕ} (Q : Common.Partition n) (e : Edge n) : ZMod 3 :=
  CanonColour Q e.2 - CanonColour Q e.1

def ThreePartitions (n : ℕ) : Finset (Common.Partition n) := by
  classical
  exact Finset.univ.filter (fun Q => IsPartition Q 3)

def SplitPosU (i : Fin 4) : Fin 9 := ⟨2 * i.val + 1, by omega⟩
def SplitPosV (i : Fin 4) : Fin 9 := ⟨2 * i.val + 2, by omega⟩

def IsSplitting (π : Equiv.Perm (Fin 9)) : Prop :=
  (∀ i : Fin 4, π (SplitPosU i) < π (SplitPosV i)) ∧
    ∀ i j : Fin 4, i < j → π (SplitPosU i) < π (SplitPosU j)

instance (π : Equiv.Perm (Fin 9)) : Decidable (IsSplitting π) := by
  unfold IsSplitting; infer_instance

def SplitEdge (π : Equiv.Perm (Fin 9)) (i : Fin 4) : Edge 9 := (π (SplitPosU i), π (SplitPosV i))

def SplitSign (π : Equiv.Perm (Fin 9)) : ZMod 3 := ((Equiv.Perm.sign π : ℤ) : ZMod 3)

def SignedSystem (y : Common.Partition 9 → ZMod 3) : Prop :=
  (∑ τ ∈ ThreePartitions 9, y τ = 0) ∧
  (∀ e e' : Edge 9, e.1 < e.2 → e'.1 < e'.2 → Disjoint (Endpoints e) (Endpoints e') →
    ∑ τ ∈ ThreePartitions 9, y τ * EdgeDiff τ e * EdgeDiff τ e' = 0) ∧
  (∀ π : Equiv.Perm (Fin 9), IsSplitting π →
    ∑ τ ∈ ThreePartitions 9, y τ * SplitSign π * ∏ i : Fin 4, EdgeDiff τ (SplitEdge π i) = 2)

end Sierksma

example : Sierksma.CanonColour ({{0,4},{1,2},{3,5,6,7,8}} : Common.Partition 9) 4 = 0 ∧
    Sierksma.CanonColour ({{0,4},{1,2},{3,5,6,7,8}} : Common.Partition 9) 2 = 1 ∧
    Sierksma.CanonColour ({{0,4},{1,2},{3,5,6,7,8}} : Common.Partition 9) 8 = 2 := by decide
example : Sierksma.IsSplitting 1 := by decide
example : Sierksma.SplitSign (Equiv.swap 0 1) = 2 := by
  simp [Sierksma.SplitSign, Equiv.Perm.sign_swap]; decide
