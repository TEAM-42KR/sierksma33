import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
noncomputable section
namespace Sierksma.FB

def allR (f : Nat → Bool) (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun _ ih k => f k && ih (Nat.succ k)) n lo

def anyR (f : Nat → Bool) (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false) (fun _ ih k => f k || ih (Nat.succ k)) n lo

def c3body (code : Nat) : Bool :=
  !(Nat.blt (idxOf code) 1855) ||
    allR (fun u => allR (fun v => (Nat.beq (digit3 code u) (digit3 code v) ==
      Nat.beq (colOf (idxOf code) u) (colOf (idxOf code) v))) 0 9) 0 9

def c4body (code : Nat) : Bool :=
  !(allR (fun c => anyR (fun v => Nat.beq (digit3 code v) c) 0 9) 0 3 &&
    allR (fun c => Nat.ble ((List.range 9).filter (fun v => Nat.beq (digit3 code v) c)).length 4) 0 3) ||
  Nat.blt (idxOf code) 1855

end Sierksma.FB

noncomputable def Sierksma.FBUtil := @Sierksma.FB.allR
