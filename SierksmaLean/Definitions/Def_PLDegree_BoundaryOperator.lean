import SierksmaLean.Definitions.Def_PLDegree_Chain
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PLDegree
namespace PLDegree
variable {V : Type*} [LinearOrder V]

def BoundaryOperator : Chain V →+ Chain V where
  toFun := boundary
  map_zero' := by simp [boundary]
  map_add' c d := Finsupp.sum_add_index' (fun s => zero_smul ℤ (faceBoundary s))
    (fun s a b => add_smul a b (faceBoundary s))

def ConeOperator (y : V) : Chain V →+ Chain V where
  toFun := cone y
  map_zero' := by simp [cone]
  map_add' c d := Finsupp.sum_add_index' (fun s => zero_smul ℤ (faceCone y s))
    (fun s a b => add_smul a b (faceCone y s))

def PairingOperator (w : Finset V → ℤ) : Chain V →+ ℤ where
  toFun c := evaluate c w
  map_zero' := by simp [evaluate]
  map_add' c d := Finsupp.sum_add_index' (fun s => zero_mul (w s))
    (fun s a b => add_mul a b (w s))
end PLDegree
