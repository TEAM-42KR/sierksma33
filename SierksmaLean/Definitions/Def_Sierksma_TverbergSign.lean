import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Common
namespace Sierksma

def LiftCoord (P : Config 9 3) (v : Fin 9) (k : ℕ) : ℝ :=
  if h : k < 3 then P v ⟨k, h⟩ else 1

def SignRow (P : Config 9 3) (col : Fin 9 → ZMod 3) (v j : Fin 9) : ℝ :=
  if j.val = 8 then 1
  else if j.val < 4 then
    (if col v = 0 then -LiftCoord P v j.val
     else if col v = 1 then LiftCoord P v j.val else 0)
  else
    (if col v = 0 then -LiftCoord P v (j.val - 4)
     else if col v = 1 then 0 else LiftCoord P v (j.val - 4))

def SignMatrix (P : Config 9 3) (col : Fin 9 → ZMod 3) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun v j => SignRow P col v j

def SignedValue (P : Config 9 3) (col : Fin 9 → ZMod 3) : ZMod 3 := by
  classical
  exact if (SignMatrix P col).det ≠ 0 ∧
      ∀ v : Fin 9, 0 < Matrix.vecMul (Pi.single (8 : Fin 9) (1 : ℝ)) (SignMatrix P col)⁻¹ v
    then (((SignType.sign (SignMatrix P col).det : SignType) : ℤ) : ZMod 3) else 0

def TverbergSign (P : Config 9 3) (Q : Common.Partition 9) : ZMod 3 := by
  classical
  exact if IsPartition Q 3 then SignedValue P (CanonColour Q) else 0

end Sierksma

example (P : Common.Config 9 3) (col : Fin 9 → ZMod 3) (v : Fin 9) (h : col v = 1) :
    Sierksma.SignMatrix P col v 0 = P v 0 ∧ Sierksma.SignMatrix P col v 3 = 1 ∧
    Sierksma.SignMatrix P col v 4 = 0 ∧ Sierksma.SignMatrix P col v 8 = 1 := by
  simp [Sierksma.SignMatrix, Sierksma.SignRow, Sierksma.LiftCoord, h]
example (P : Common.Config 9 3) (col : Fin 9 → ZMod 3) (v : Fin 9) (h : col v = 0) :
    Sierksma.SignMatrix P col v 2 = -P v 2 ∧ Sierksma.SignMatrix P col v 6 = -P v 2 ∧
    Sierksma.SignMatrix P col v 7 = -1 := by
  simp [Sierksma.SignMatrix, Sierksma.SignRow, Sierksma.LiftCoord, h]
example (P : Common.Config 9 3) (col : Fin 9 → ZMod 3) (v : Fin 9) (h : col v = 2) :
    Sierksma.SignMatrix P col v 1 = 0 ∧ Sierksma.SignMatrix P col v 5 = P v 1 ∧
    Sierksma.SignMatrix P col v 7 = 1 := by
  have h0 : col v ≠ 0 := by rw [h]; decide
  have h1 : col v ≠ 1 := by rw [h]; decide
  simp [Sierksma.SignMatrix, Sierksma.SignRow, Sierksma.LiftCoord, h0, h1]
