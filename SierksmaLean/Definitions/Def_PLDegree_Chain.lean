import Mathlib
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace PLDegree

abbrev Chain (V : Type*) := (Finset V) →₀ ℤ

variable {V : Type*} [LinearOrder V]

def rank (s : Finset V) (v : V) : ℕ := (s.filter (fun w => w < v)).card

def incidence (s : Finset V) (v : V) : ℤ := (-1) ^ rank s v

def faceBoundary (s : Finset V) : Chain V :=
  ∑ v ∈ s, Finsupp.single (s.erase v) (incidence s v)

def boundary (c : Chain V) : Chain V :=
  c.sum (fun s a => a • faceBoundary s)

def faceCone (y : V) (s : Finset V) : Chain V :=
  if y ∈ s then 0 else Finsupp.single (insert y s) (incidence (insert y s) y)

def cone (y : V) (c : Chain V) : Chain V :=
  c.sum (fun s a => a • faceCone y s)

def link (y : V) (c : Chain V) : Chain V :=
  c.sum (fun s a => if y ∈ s then a • Finsupp.single (s.erase y) (incidence s y) else 0)

def moveVertex (y y' : V) (c : Chain V) : Chain V :=
  c - cone y (link y c) + cone y' (link y c)

def bubble (y y' : V) (c : Chain V) : Chain V := cone y' (cone y (link y c))

def Homogeneous (k : ℕ) (c : Chain V) : Prop := ∀ s ∈ c.support, s.card = k

def Fresh (y : V) (c : Chain V) : Prop := ∀ s ∈ c.support, y ∉ s

def IsCycle (c : Chain V) : Prop := boundary c = 0

def evaluate (c : Chain V) (w : Finset V → ℤ) : ℤ := c.sum (fun s a => a * w s)

def listSign {k : ℕ} (t : Fin k → V) : ℤ :=
  (-1) ^ ((Finset.univ.filter (fun ij : Fin k × Fin k => ij.1 < ij.2 ∧ t ij.2 < t ij.1)).card)

def listedFace {k : ℕ} (t : Fin k → V) : Chain V :=
  Finsupp.single (Finset.univ.image t) (listSign t)

def relabel (f : V → V) (c : Chain V) : Chain V :=
  c.sum (fun s a => a • listedFace (fun i : Fin s.card => f (s.orderEmbOfFin rfl i)))

def augment {n : ℕ} (x : Fin n → ℝ) (a : ℝ) (j : Fin (n+1)) : ℝ :=
  if h : j.val < n then x ⟨j.val, h⟩ else a

def augmentedMatrix {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V)
    (hs : s.card = n + 1) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => augment (F (s.orderEmbOfFin hs i)) 1 j

def originRow (n : ℕ) : Fin (n+1) → ℝ := Pi.single (Fin.last n) 1

def barycentric {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V)
    (hs : s.card = n+1) : Fin (n+1) → ℝ :=
  Matrix.vecMul (originRow n) (augmentedMatrix F s hs)⁻¹

def augmentedDet {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V) : ℝ :=
  if hs : s.card = n+1 then (augmentedMatrix F s hs).det else 0

def linearDet {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V) : ℝ :=
  if hs : s.card = n then Matrix.det (fun i j : Fin n => F (s.orderEmbOfFin hs i) j) else 0

def simplexDegree {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V) : ℤ :=
  if hs : s.card = n+1 then
    if (augmentedMatrix F s hs).det ≠ 0 ∧ ∀ i, 0 < barycentric F s hs i
    then (SignType.sign (augmentedMatrix F s hs).det : ℤ) else 0
  else 0

def signedCount {n : ℕ} (F : V → Fin n → ℝ) (c : Chain V) : ℤ :=
  evaluate c (simplexDegree F)

def hull {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V) : Set (Fin n → ℝ) :=
  convexHull ℝ (F '' (s : Set V))

def NoBoundaryZero {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V) : Prop :=
  ∀ t : Finset V, t ⊂ s → (0 : Fin n → ℝ) ∉ hull F t

def SimplexGP {n : ℕ} (F : V → Fin n → ℝ) (s : Finset V) : Prop :=
  s.card = n+1 ∧ augmentedDet F s ≠ 0 ∧ ∀ v ∈ s, linearDet F (s.erase v) ≠ 0

def ChainGP {n : ℕ} (F : V → Fin n → ℝ) (c : Chain V) : Prop :=
  ∀ s ∈ c.support, SimplexGP F s

def RayHits {n : ℕ} (F : V → Fin n → ℝ) (u : Fin n → ℝ) (s : Finset V) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t • u ∈ hull F s

def rayMatrix {n : ℕ} (F : V → Fin n → ℝ) (u : Fin n → ℝ) (s : Finset V)
    (hs : s.card = n) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if h : i.val = 0 then augment u 0 j
    else augment (F (s.orderEmbOfFin hs ⟨i.val-1, by omega⟩)) 1 j

def rayDet {n : ℕ} (F : V → Fin n → ℝ) (u : Fin n → ℝ) (s : Finset V) : ℝ :=
  if hs : s.card = n then (rayMatrix F u s hs).det else 0

def rayWeight {n : ℕ} (F : V → Fin n → ℝ) (u : Fin n → ℝ) (s : Finset V) : ℤ :=
  if RayHits F u s then (SignType.sign (rayDet F u s) : ℤ) else 0

def RayGeneric {n : ℕ} (F : V → Fin n → ℝ) (u : Fin n → ℝ) (s : Finset V) : Prop :=
  u ≠ 0 ∧ (∀ v ∈ s, rayDet F u (s.erase v) ≠ 0) ∧
    ∀ t : Finset V, t ⊆ s → t.card + 2 ≤ s.card → ¬ RayHits F u t

end PLDegree
