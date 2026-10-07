import Mathlib
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Common
abbrev Block (n : ℕ) := Finset (Fin n)
abbrev Partition (n : ℕ) := Finset (Block n)
abbrev Config (n d : ℕ) := Fin n → (Fin d → ℝ)
def BlocksOn {n : ℕ} (Q : Partition n) (X : Block n) : Prop :=
 (∀ A ∈ Q, A.Nonempty ∧ A ⊆ X) ∧
 (∀ A ∈ Q, ∀ B ∈ Q, A ≠ B → Disjoint A B) ∧ Q.biUnion id = X
def IsPartition {n : ℕ} (Q : Partition n) (r : ℕ) : Prop := BlocksOn Q Finset.univ ∧ Q.card = r
def HasCommonHull {n d : ℕ} (P : Config n d) (Q : Partition n) : Prop :=
 ∃ z : Fin d → ℝ, ∀ A ∈ Q, z ∈ convexHull ℝ (P '' (↑A : Set (Fin n)))
def IsTverberg {n d : ℕ} (r : ℕ) (P : Config n d) (Q : Partition n) : Prop :=
 IsPartition Q r ∧ HasCommonHull P Q
def TverbergPartitions {n d : ℕ} (r : ℕ) (P : Config n d) : Finset (Partition n) := by
 classical
 exact Finset.univ.filter (IsTverberg r P)
def TverbergCount {n d : ℕ} (r : ℕ) (P : Config n d) : ℕ := (TverbergPartitions r P).card
def AffineGP {n d : ℕ} (P : Config n d) : Prop :=
 ∀ A : Block n, A.card ≤ d+1 → AffineIndependent ℝ (fun i : {v // v ∈ A} => P i.val)
def StrongGP (P : Config 9 3) : Prop := AffineGP P ∧
 ∀ E T T' : Block 9, E.card = 2 → T.card = 3 → T'.card = 3 →
 Disjoint E T → Disjoint E T' → Disjoint T T' →
 ¬ ∃ z : Fin 3 → ℝ, z ∈ affineSpan ℝ (P '' (↑E : Set (Fin 9))) ∧
 z ∈ affineSpan ℝ (P '' (↑T : Set (Fin 9))) ∧ z ∈ affineSpan ℝ (P '' (↑T' : Set (Fin 9)))
def OrderDet {n d : ℕ} (P : Config n d) (i : Fin (d+1) → Fin n) : ℝ :=
 Matrix.det (fun a b : Fin (d+1) => Fin.cases 1 (fun k : Fin d => P (i a) k) b)
def SameOrderType {n d : ℕ} (P Q : Config n d) : Prop :=
 ∀ i : Fin (d+1) → Fin n, (0 < OrderDet P i ↔ 0 < OrderDet Q i) ∧
 (OrderDet P i = 0 ↔ OrderDet Q i = 0)
def TypeIs {n : ℕ} (Q : Partition n) (sizes : Multiset ℕ) : Prop := Q.val.map Finset.card = sizes
def TypeCount {n d : ℕ} (P : Config n d) (sizes : Multiset ℕ) : ℕ := by
 classical
 exact ((TverbergPartitions 3 P).filter (fun Q => TypeIs Q sizes)).card
def SingletonCount {n d : ℕ} (P : Config n d) (v : Fin n) : ℕ := by
 classical
 exact ((TverbergPartitions 3 P).filter (fun Q => ({v} : Block n) ∈ Q)).card
end Common
