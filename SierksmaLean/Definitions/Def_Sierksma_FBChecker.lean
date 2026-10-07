import SierksmaLean.Definitions.Def_Sierksma_FBTablesB
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
set_option autoImplicit false
noncomputable section
open Common
namespace Sierksma.FB

def M20 : Nat := 1048575

def fetch (l : List Nat) : Option (Nat × List Nat) :=
  match l with
  | [] => none
  | s :: r =>
    cond (Nat.beq s 0)
      (match r with
       | [] => none
       | s' :: r' => some (Nat.land s' M20, Nat.shiftRight s' 20 :: r'))
      (some (Nat.land s M20, Nat.shiftRight s 20 :: r))

def field (x f : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 4 f)) 15

def neg3 (c : Nat) : Nat := Nat.mod (Nat.sub 3 c) 3

def dI (i u v : Nat) : Nat := Nat.mod (Nat.sub (Nat.add (colOf i v) 3) (colOf i u)) 3

def splE (m k : Nat) : Nat := Nat.land (Nat.shiftRight (spl m) (Nat.mul 6 k)) 63

def twistDigit (c k : Nat) : Nat := Nat.mod (Nat.div c (Nat.pow 3 k)) 3

def covOf (g : Nat) : Nat :=
  let m := Nat.div g 81
  let c := Nat.mod g 81
  let e0 := splE m 0
  let e1 := splE m 1
  let e2 := splE m 2
  let e3 := splE m 3
  let c0 := twistDigit c 0
  let c1 := twistDigit c 1
  let c2 := twistDigit c 2
  let c3 := twistDigit c 3
  Nat.lor
    (Nat.land (Nat.land (nt (Nat.add (Nat.mul 3 e0) c0)) (nt (Nat.add (Nat.mul 3 e1) c1)))
              (Nat.land (nt (Nat.add (Nat.mul 3 e2) c2)) (nt (Nat.add (Nat.mul 3 e3) c3))))
    (Nat.land (Nat.land (nt (Nat.add (Nat.mul 3 e0) (neg3 c0))) (nt (Nat.add (Nat.mul 3 e1) (neg3 c1))))
              (Nat.land (nt (Nat.add (Nat.mul 3 e2) (neg3 c2))) (nt (Nat.add (Nat.mul 3 e3) (neg3 c3)))))

def witLoop (C K fw n : Nat) : List Nat → Nat → Option (List Nat) :=
  Nat.rec (motive := fun _ => List Nat → Nat → Option (List Nat))
    (fun l acc => cond (Nat.beq acc 0) (some l) none)
    (fun _ ih l acc =>
      match fetch l with
      | none => none
      | some (t, l1) =>
        let cv := covOf (Nat.shiftRight t 3)
        cond (Nat.beq (Nat.land C cv) 0 &&
              (Nat.beq fw 0 || Nat.beq (Nat.land (Nat.land K cv) (intt (Nat.sub fw 1))) (Nat.land K cv)))
          (ih l1 (Nat.land acc cv)) none)
    n

def readN (n : Nat) : List Nat → Option (List Nat × List Nat) :=
  Nat.rec (motive := fun _ => List Nat → Option (List Nat × List Nat))
    (fun l => some ([], l))
    (fun _ ih l =>
      match fetch l with
      | none => none
      | some (t, l1) =>
        match ih l1 with
        | none => none
        | some (xs, l2) => some (Nat.shiftRight t 3 :: xs, l2))
    n

def memBits (mem : List Nat) : Nat := List.foldr (fun p acc => Nat.lor (Nat.shiftLeft 1 p) acc) 0 mem
def memMult (mem : List Nat) : Nat := List.foldr (fun p acc => Nat.add (peOf p) acc) 0 mem

def incrAux : Nat → List Nat → Bool
  | _, [] => true
  | lo, p :: ps => Nat.ble lo p && Nat.blt p 1855 && incrAux (Nat.succ p) ps
def incr (mem : List Nat) : Bool := incrAux 0 mem

def qu (q : Nat) : Nat := Nat.mod q 9
def qv (q : Nat) : Nat := Nat.mod (Nat.div q 9) 9
def qu' (q : Nat) : Nat := Nat.mod (Nat.div q 81) 9
def qv' (q : Nat) : Nat := Nat.mod (Nat.div q 729) 9
def quadOK (q : Nat) : Bool :=
  Nat.blt (qu q) (qv q) && Nat.blt (qu' q) (qv' q) && !(Nat.beq (qu q) (qu' q)) &&
  !(Nat.beq (qu q) (qv' q)) && !(Nat.beq (qv q) (qu' q)) && !(Nat.beq (qv q) (qv' q))

def zAt (mask j : Nat) : Nat := cond (Nat.testBit mask j) 2 1
def sumZ (w : Nat → Nat) (mask : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | j, p :: ps => Nat.add (Nat.mul (zAt mask j) (w p)) (sumZ w mask (Nat.succ j) ps)
def w2 (q p : Nat) : Nat := Nat.mul (dI p (qu q) (qv q)) (dI p (qu' q) (qv' q))

def signOK (mem : List Nat) (q1 q2 : Nat) : Bool :=
  (List.range (Nat.pow 2 mem.length)).all (fun mask =>
    !(Nat.beq (Nat.mod (sumZ (fun _ => 1) mask 0 mem) 3) 0 &&
      Nat.beq (Nat.mod (sumZ (w2 q1) mask 0 mem) 3) 0 &&
      Nat.beq (Nat.mod (sumZ (w2 q2) mask 0 mem) 3) 0))

def solParse (C n : Nat) (l : List Nat) : Option (List Nat) :=
  match readN n l with
  | none => none
  | some (mem, l1) =>
    match readN 2 l1 with
    | none => none
    | some (qs, l2) =>
      match qs with
      | [q1, q2] =>
        cond (incr mem && Nat.beq (memBits mem) C && quadOK q1 && quadOK q2 && signOK mem q1 q2)
          (some l2) none
      | _ => none

def nth? : List (Nat × Nat × Nat) → Nat → Option (Nat × Nat × Nat)
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

def step (caps : Nat) (ext : List (Nat × Nat × Nat))
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
         cond (Nat.beq (Nat.land C cv) 0 && (Nat.beq b 0 || Nat.beq (Nat.land K cv) 0)) (some l1) none)
      (cond (Nat.beq op 2)
        (let n := Nat.mod g 64
         let fw := Nat.div g 64
         cond (Nat.ble 1 n &&
               cond (Nat.beq fw 0) (Nat.ble b 1)
                 (Nat.ble fw 37 && Nat.ble (field caps (Nat.sub fw 1)) (Nat.add (field M (Nat.sub fw 1)) 1)))
           (witLoop C K fw n l1 K) none)
      (cond (Nat.beq op 3)
        (cond (Nat.blt g 37 && Nat.ble (field caps g) (field M g))
          (r 0 l1 C (Nat.sub K (Nat.land K (intt g))) b M 0) none)
      (cond (Nat.beq op 4)
        (let cv := covOf g
         cond (Nat.beq (Nat.land C cv) 0 && Nat.ble 1 b) (r 1 l1 C K b M (Nat.land K cv)) none)
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

def chk (caps : Nat) (ext : List (Nat × Nat × Nat)) (fuel : Nat) :
    Nat → List Nat → Nat → Nat → Nat → Nat → Nat → Option (List Nat) :=
  Nat.rec (motive := fun _ => Nat → List Nat → Nat → Nat → Nat → Nat → Nat → Option (List Nat))
    (fun _ _ _ _ _ _ _ => none) (fun _ ih => step caps ext ih) fuel

def KMASK : Nat := Nat.sub (Nat.pow 2 1855) 1

def run (s mem : List Nat) (K b caps : Nat) (ext : List (Nat × Nat × Nat)) : Bool :=
  incr mem && Nat.ble (Nat.add mem.length b) 15 && Nat.beq (Nat.land (memBits mem) K) 0 &&
  Nat.ble K KMASK &&
  (match chk caps ext 4000000 0 s (memBits mem) K b (memMult mem) 0 with
   | none => false
   | some _ => true)

def coversIdx (S : Finset ℕ) : Prop := ∀ g < 76545, ∃ i ∈ S, Nat.testBit (covOf g) i = true

def signedIdx (S : Finset ℕ) : Prop :=
  ∃ z : ℕ → ZMod 3, (∀ i ∈ S, z i ≠ 0) ∧ (∑ i ∈ S, z i = 0) ∧
    ∀ u v u' v' : ℕ, u < v → u' < v' → v < 9 → v' < 9 → u ≠ u' → u ≠ v' → v ≠ u' → v ≠ v' →
      ∑ i ∈ S, z i * ((dI i u v : ℕ) : ZMod 3) * ((dI i u' v' : ℕ) : ZMod 3) = 0

def mult (S : Finset ℕ) (f : ℕ) : ℕ := (S.filter (fun i => Nat.testBit (intt f) i = true)).card

def capOK (S : Finset ℕ) (caps : ℕ) : Prop := ∀ f < 37, mult S f ≤ field caps f

def Good (C K b caps : ℕ) : Prop :=
  ∀ S : Finset ℕ, (∀ i, Nat.testBit C i = true → i ∈ S) →
    (∀ i ∈ S, Nat.testBit C i = true ∨ Nat.testBit K i = true) →
    (S.filter (fun i => Nat.testBit C i = false)).card ≤ b →
    capOK S caps → coversIdx S → ¬ signedIdx S

def partOf (i : ℕ) : Common.Partition 9 :=
  (Finset.univ : Finset (Fin 3)).image
    (fun c => Finset.univ.filter (fun v : Fin 9 => colOf i v.val = c.val))

def idxSupp (y : Common.Partition 9 → ZMod 3) : Finset ℕ :=
  (Finset.range 1855).filter (fun i => y (partOf i) ≠ 0)

def edgeOf (f : ℕ) : Edge 9 :=
  (⟨Nat.mod (eu f) 9, Nat.mod_lt _ (by decide)⟩, ⟨Nat.mod (ev f) 9, Nat.mod_lt _ (by decide)⟩)

def constraintOf (g : ℕ) : PairConstraint 9 :=
  { matching := {edgeOf (splE (g / 81) 0), edgeOf (splE (g / 81) 1), edgeOf (splE (g / 81) 2),
      edgeOf (splE (g / 81) 3)}
    twists := fun e =>
      if e = edgeOf (splE (g / 81) 0) then ((twistDigit (g % 81) 0 : ℕ) : ZMod 3)
      else if e = edgeOf (splE (g / 81) 1) then ((twistDigit (g % 81) 1 : ℕ) : ZMod 3)
      else if e = edgeOf (splE (g / 81) 2) then ((twistDigit (g % 81) 2 : ℕ) : ZMod 3)
      else if e = edgeOf (splE (g / 81) 3) then ((twistDigit (g % 81) 3 : ℕ) : ZMod 3)
      else 0 }

def pAt (p v : ℕ) : ℕ := Nat.land (Nat.shiftRight p (Nat.mul 4 v)) 15

def validPerm (p : ℕ) : Bool :=
  (List.range 9).all (fun v => Nat.blt (pAt p v) 9) &&
  (List.range 9).all (fun v => (List.range 9).all (fun w => Nat.beq v w || !(Nat.beq (pAt p v) (pAt p w))))

def relCode (p i : ℕ) : ℕ :=
  List.foldr (fun v acc => Nat.add (Nat.mul (colOf i v) (Nat.pow 3 (pAt p v))) acc) 0 (List.range 9)

def relIdx (p i : ℕ) : ℕ := idxOf (relCode p i)

def eIdx (a b : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.sub (Nat.mul a 8) (Nat.div (Nat.mul a (Nat.sub a 1)) 2)) b) (Nat.add a 1)

def epOf (p f : ℕ) : ℕ :=
  cond (Nat.beq f 36) 36
    (cond (Nat.blt (pAt p (eu f)) (pAt p (ev f))) (eIdx (pAt p (eu f)) (pAt p (ev f)))
      (eIdx (pAt p (ev f)) (pAt p (eu f))))

def digit3 (code k : Nat) : Nat := Nat.mod (Nat.div code (Nat.pow 3 k)) 3

def cntBetween (a b : Nat) (excl : List Nat) : Nat :=
  ((List.range 9).filter (fun w => Nat.blt a w && Nat.blt w b && !(excl.elem w))).length

def mRank (e0 e1 e2 e3 : Nat) : Nat :=
  let a0 := eu e0
  let b0 := ev e0
  let a1 := eu e1
  let b1 := ev e1
  let a2 := eu e2
  let b2 := ev e2
  let s := Nat.sub 36 (a0 + b0 + a1 + b1 + a2 + b2 + eu e3 + ev e3)
  105 * s + 15 * cntBetween a0 b0 [s] + 3 * cntBetween a1 b1 [s, a0, b0] +
    cntBetween a2 b2 [s, a0, b0, a1, b1]

def edisj (f f' : Nat) : Bool :=
  !(Nat.beq (eu f) (eu f')) && !(Nat.beq (eu f) (ev f')) && !(Nat.beq (ev f) (eu f')) && !(Nat.beq (ev f) (ev f'))

end Sierksma.FB

noncomputable def Sierksma.FBChecker := @Sierksma.FB.run
