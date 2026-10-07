import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
noncomputable section
namespace Sierksma.FB

def witLoopR (C K fw n : Nat) : List Nat → Nat → Option (List Nat) :=
  Nat.rec (motive := fun _ => List Nat → Nat → Option (List Nat))
    (fun l acc => cond (Nat.beq acc 0) (some l) none)
    (fun _ ih l acc =>
      match fetch l with
      | none => none
      | some (t, l1) =>
        let g := Nat.shiftRight t 3
        let cv := covOf g
        cond (Nat.blt g 76545 && Nat.beq (Nat.land C cv) 0 &&
              (Nat.beq fw 0 || Nat.beq (Nat.land (Nat.land K cv) (intt (Nat.sub fw 1))) (Nat.land K cv)))
          (ih l1 (Nat.land acc cv)) none)
    n

def stepR (caps : Nat) (ext : List (Nat × Nat × Nat))
    (r : Nat → List Nat → Nat → Nat → Nat → Nat → Nat → Option (List Nat))
    (mode : Nat) (l : List Nat) (C K b M A : Nat) : Option (List Nat) :=
  match fetch l with
  | none => none
  | some (t, l1) =>
    let op := Nat.land t 7
    let g := Nat.shiftRight t 3
    cond (Nat.beq mode 0)
      (cond (Nat.beq op 0)
        (match nth? ext (Nat.sub g 1) with
         | none => none
         | some (C', K', b') =>
           cond (Nat.ble 1 g && Nat.beq C' C && Nat.beq K' K && Nat.beq b' b) (some l1) none)
      (cond (Nat.beq op 1)
        (let cv := covOf g
         cond (Nat.blt g 76545 && Nat.beq (Nat.land C cv) 0 && (Nat.beq b 0 || Nat.beq (Nat.land K cv) 0))
           (some l1) none)
      (cond (Nat.beq op 2)
        (let n := Nat.mod g 64
         let fw := Nat.div g 64
         cond (Nat.ble 1 n &&
               cond (Nat.beq fw 0) (Nat.ble b 1)
                 (Nat.ble fw 37 && Nat.ble (field caps (Nat.sub fw 1)) (Nat.add (field M (Nat.sub fw 1)) 1)))
           (witLoopR C K fw n l1 K) none)
      (cond (Nat.beq op 3)
        (cond (Nat.blt g 37 && Nat.ble (field caps g) (field M g))
          (r 0 l1 C (Nat.sub K (Nat.land K (intt g))) b M 0) none)
      (cond (Nat.beq op 4)
        (let cv := covOf g
         cond (Nat.blt g 76545 && Nat.beq (Nat.land C cv) 0 && Nat.ble 1 b) (r 1 l1 C K b M (Nat.land K cv)) none)
      (cond (Nat.beq op 7)
        (cond (Nat.beq b 0) (solParse C g l1) none)
        none))))))
      (cond (Nat.beq op 5)
        (cond (Nat.beq A 0) (some l1) none)
      (cond (Nat.beq op 6)
        (let lb := Nat.shiftLeft 1 g
         cond (Nat.beq (Nat.land A lb) 0) none
          (match r 0 l1 (Nat.lor C lb) (Nat.sub K lb) (Nat.sub b 1) (Nat.add M (peOf g)) 0 with
           | none => none
           | some l2 => r 1 l2 C (Nat.sub K lb) b M (Nat.sub A lb)))
        none))

def chkR (caps : Nat) (ext : List (Nat × Nat × Nat)) (fuel : Nat) :
    Nat → List Nat → Nat → Nat → Nat → Nat → Nat → Option (List Nat) :=
  Nat.rec (motive := fun _ => Nat → List Nat → Nat → Nat → Nat → Nat → Nat → Option (List Nat))
    (fun _ _ _ _ _ _ _ => none) (fun _ ih => stepR caps ext ih) fuel

def runR (s mem : List Nat) (K b caps : Nat) (ext : List (Nat × Nat × Nat)) : Bool :=
  incr mem && Nat.ble (Nat.add mem.length b) 15 && Nat.beq (Nat.land (memBits mem) K) 0 &&
  Nat.ble K KMASK &&
  (match chkR caps ext 4000000 0 s (memBits mem) K b (memMult mem) 0 with
   | none => false
   | some _ => true)

end Sierksma.FB

noncomputable def Sierksma.FBRun := @Sierksma.FB.runR
