import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open PLDegree
open scoped BigOperators
noncomputable section
namespace Sierksma
def L6Old (r : Fin 8) (i : Fin 3) : ℕ := 6*(r.val/2)+r.val%2+2*i.val
def L6New (r : Fin 8) (i : Fin 3) : ℕ := 27+L6Old r i
def L6Swap (r : Fin 8) : Equiv.Perm ℕ :=
  (Equiv.swap (L6Old r 0) (L6New r 0)).trans
    ((Equiv.swap (L6Old r 1) (L6New r 1)).trans (Equiv.swap (L6Old r 2) (L6New r 2)))
def L6Replaced (r : Fin 8) : Chain ℕ := relabel (L6Swap r) HexCycle
def L6Map (x y : EngineParams) (v : ℕ) : W8 :=
  if v<27 then EngineMap x v else if v<51 then EngineMap y (v-27) else 0
def L6Shift (v : ℕ) : ℕ :=
  if v<27 then ShiftVertex v else if v<51 then 27+ShiftVertex (v-27) else v
def L6Aux (x : EngineParams) (r : Fin 8) (u : W8) : EngineParams :=
  Function.update x r.castSucc u
end Sierksma
