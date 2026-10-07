import SierksmaLean.Definitions.Def_PLDegree_Chain
import SierksmaLean.Definitions.Def_Sierksma_TverbergSign
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Common PLDegree

namespace Sierksma

abbrev W8 := Fin 8 → ℝ
abbrev EngineParams := Fin 9 → W8

def R8 (w : W8) : W8 := fun j =>
  if h : j.val < 4 then -w ⟨j.val+4, by omega⟩
  else w ⟨j.val-4, by omega⟩ - w j

def RPower (k : ℕ) (w : W8) : W8 := (R8^[k]) w

def ShiftVertex (v : ℕ) : ℕ :=
  if v < 24 then 6*(v/6) + (v%6+2)%6
  else if v < 27 then 24+(v-24+1)%3 else v

def HexTuple (a : Fin 4 → Fin 6) (k : Fin 8) : ℕ :=
  6*(k.val/2) + if k.val%2=0 then (a ⟨k.val/2, by omega⟩).val
    else ((a ⟨k.val/2, by omega⟩).val+1)%6

def HexCycle : PLDegree.Chain ℕ :=
  ∑ a : Fin 4 → Fin 6, PLDegree.listedFace (HexTuple a)

def EngineCone (j : Fin 3) : PLDegree.Chain ℕ := PLDegree.cone (24+j.val) HexCycle

def EngineMap (x : EngineParams) (v : ℕ) : W8 :=
  if h : v < 24 then
    RPower (v%6/2) (x ⟨2*(v/6)+v%2, by omega⟩)
  else if h' : v < 27 then RPower (v-24) (x 8) else 0

def EngineGeneric (x : EngineParams) : Prop :=
  ∀ j : Fin 3, PLDegree.ChainGP (EngineMap x) (EngineCone j)

def ConeCount (x : EngineParams) (j : Fin 3) : ℤ :=
  PLDegree.signedCount (EngineMap x) (EngineCone j)

def OneOrbitMove (x y : EngineParams) : Prop :=
  ∃ r : Fin 9, ∀ i : Fin 9, i ≠ r → x i = y i

def CloseParams (x y : EngineParams) (eps : ℝ) : Prop :=
  ∀ i j, |x i j-y i j| < eps

def ModelParamsQ (r : Fin 9) (j : Fin 8) : ℚ :=
  if r.val < 8 then
    if j.val = r.val/2 then 1
    else if j.val = r.val/2+4 ∧ r.val%2=1 then 1 else 0
  else if j.val < 4 then -2/9 else -1/9

def ModelParams : EngineParams := fun r j => (ModelParamsQ r j : ℝ)

def HexCoordQ (a : Fin 6) (b : Fin 2) : ℚ :=
  if a.val=0 then (if b.val=0 then 1 else 0)
  else if a.val=1 then 1
  else if a.val=2 then (if b.val=0 then 0 else 1)
  else if a.val=3 then (if b.val=0 then -1 else 0)
  else if a.val=4 then -1
  else (if b.val=0 then 0 else -1)

def ModelFacetMatrixQ (a : Fin 4 → Fin 6) : Matrix (Fin 9) (Fin 9) ℚ := fun i j =>
  if hj : j.val=8 then 1
  else if hi : i.val=0 then ModelParamsQ 8 ⟨j.val, by omega⟩
  else if j.val%4 = (i.val-1)/2 then
    HexCoordQ ⟨((a ⟨(i.val-1)/2, by omega⟩).val + (i.val-1)%2)%6, Nat.mod_lt _ (by omega)⟩
      ⟨j.val/4, by omega⟩
  else 0

def LastCofactorQ (M : Matrix (Fin 9) (Fin 9) ℚ) (i : Fin 9) : ℚ :=
  (-1) ^ (i.val+8) * Matrix.det (fun r c : Fin 8 => M (i.succAbove r) c.castSucc)

def ModelCountQ : ℤ :=
  ∑ a : Fin 4 → Fin 6,
    if (ModelFacetMatrixQ a).det ≠ 0 ∧
        ∀ i, 0 < LastCofactorQ (ModelFacetMatrixQ a) i / (ModelFacetMatrixQ a).det
    then (SignType.sign (ModelFacetMatrixQ a).det : ℤ) else 0

def ModelExactCheck : Prop :=
  (∀ a : Fin 4 → Fin 6, (ModelFacetMatrixQ a).det ≠ 0 ∧
     ∀ i, LastCofactorQ (ModelFacetMatrixQ a) i ≠ 0) ∧ ModelCountQ=1

def TestW (P : Config 9 3) (v : Fin 9) (c : ZMod 3) : W8 := fun j =>
  if j.val < 4 then
    if c=0 then -LiftCoord P v j.val else if c=1 then LiftCoord P v j.val else 0
  else if c=0 then -LiftCoord P v (j.val-4)
    else if c=1 then 0 else LiftCoord P v (j.val-4)

def TestParams (P : Config 9 3) (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) : EngineParams :=
  fun r => if h : r.val<8 then
      if r.val%2=0 then TestW P (pi (SplitPosU ⟨r.val/2, by omega⟩)) 0
      else TestW P (pi (SplitPosV ⟨r.val/2, by omega⟩)) (c ⟨r.val/2, by omega⟩-1)
    else TestW P (pi 0) 0

def TwistPhi (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (v : ℕ) : ℕ :=
  if h : v<24 then
    let i : Fin 4 := ⟨v/6, by omega⟩
    if v%2=0 then 3*(pi (SplitPosU i)).val + (v%6/2)
    else 3*(pi (SplitPosV i)).val + (c i-1+(v%6/2 : ℕ)).val
  else if v<27 then 3*(pi 0).val+(v-24) else v

def ColorShiftVertex (v : ℕ) : ℕ := if v<27 then 3*(v/3)+(v%3+1)%3 else v

def TargetTestMap (P : Config 9 3) (v : ℕ) : W8 :=
  if h : v<27 then TestW P ⟨v/3, by omega⟩ (v%3 : ℕ) else 0

def chi (a : ZMod 3) : ℤ := if a=0 then 0 else if a=1 then 1 else -1

def ColorFacet (col : Fin 9 → ZMod 3) : Finset ℕ :=
  Finset.univ.image (fun v : Fin 9 => 3*v.val+(col v).val)

def ColorChain (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) : PLDegree.Chain ℕ :=
  ∑ col : Fin 9 → ZMod 3,
    if col (pi 0)=0 then
      Finsupp.single (ColorFacet col)
        (((Equiv.Perm.sign pi : ℤ)) * ∏ i : Fin 4,
          chi (col (pi (SplitPosV i))-col (pi (SplitPosU i))-c i))
    else 0

def ColorBlock (A : Finset (Fin 9)) (col : Fin 9 → ZMod 3) (j : ZMod 3) : Finset (Fin 9) :=
  A.filter (fun v => col v=j)

def ColoredZero (P : Config 9 3) (A : Finset (Fin 9)) (col : Fin 9 → ZMod 3) : Prop :=
  ∃ w : Fin 9 → ℝ, (∀ v, 0 ≤ w v) ∧ (∀ v, v ∉ A → w v=0) ∧
    (∑ v, w v)=1 ∧ (∑ v, w v • TestW P v (col v))=0

def ColoredCommonHull (P : Config 9 3) (A : Finset (Fin 9)) (col : Fin 9 → ZMod 3) : Prop :=
  (∀ j : ZMod 3, (ColorBlock A col j).Nonempty) ∧
    ∃ z : Fin 3 → ℝ, ∀ j : ZMod 3,
      z ∈ convexHull ℝ (P '' (ColorBlock A col j : Set (Fin 9)))

def ColoredBlocks (A : Finset (Fin 9)) (col : Fin 9 → ZMod 3) : Common.Partition 9 :=
  ((Finset.univ : Finset (ZMod 3)).image (ColorBlock A col)).filter Finset.Nonempty

def TripleDet (P : Config 9 3) (t : Fin 3 → Fin 9) (q : Fin 3 → ℝ) : ℝ :=
  Matrix.det ![P (t 1)-P (t 0), P (t 2)-P (t 0), q]

def QPoly (P : Config 9 3) (e : Edge 9) (t t' : Fin 3 → Fin 9) : ℝ :=
  TripleDet P t (P e.2-P e.1) * TripleDet P t' (P e.1-P (t' 0)) -
    TripleDet P t' (P e.2-P e.1) * TripleDet P t (P e.1-P (t 0))

def G1Polynomial (P : Config 9 3) : Prop :=
  ∀ a : Fin 4 → Fin 9, Function.Injective a →
    Matrix.det (fun i j : Fin 4 => LiftCoord P (a i) j.val) ≠ 0

def G4Polynomial (P : Config 9 3) : Prop :=
  ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9,
    Function.Injective t → Function.Injective t' →
    Disjoint (Endpoints e) (Finset.univ.image t) →
    Disjoint (Endpoints e) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → QPoly P e t t' ≠ 0

def LastCofactor (M : Matrix (Fin 9) (Fin 9) ℝ) (i : Fin 9) : ℝ :=
  (-1) ^ (i.val+8) * Matrix.det (fun r c : Fin 8 => M (i.succAbove r) c.castSucc)

def SignGP (P : Config 9 3) (Q : Common.Partition 9) : Prop :=
  (SignMatrix P (CanonColour Q)).det ≠ 0 ∧
    ∀ v, LastCofactor (SignMatrix P (CanonColour Q)) v ≠ 0

def GenericLocus : Set (Config 9 3) :=
  {P | G1Polynomial P ∧ G4Polynomial P ∧ ∀ Q ∈ Universe 3, SignGP P Q}

def TwistPolynomial (y : Common.Partition 9 → ZMod 3) (pi : Equiv.Perm (Fin 9))
    (c : Fin 4 → ZMod 3) : ZMod 3 :=
  SplitSign pi * ∑ Q ∈ ThreePartitions 9,
    y Q * ((∏ i : Fin 4, (EdgeDiff Q (SplitEdge pi i)-c i)) +
      (∏ i : Fin 4, (-EdgeDiff Q (SplitEdge pi i)-c i)))

def MultiaffineEval (a : Finset (Fin 4) → ZMod 3) (c : Fin 4 → ZMod 3) : ZMod 3 :=
  ∑ s : Finset (Fin 4), a s * ∏ i ∈ s, c i

abbrev RQConfig := Fin 9 → Fin 3 → ℚ

def RQLift (P : RQConfig) (v : Fin 9) (k : ℕ) : ℚ :=
  if h : k<3 then P v ⟨k,h⟩ else 1

def RQSignMatrix (P : RQConfig) (col : Fin 9 → ZMod 3) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun v j => if j.val=8 then 1
    else if j.val<4 then (if col v=0 then -RQLift P v j.val
      else if col v=1 then RQLift P v j.val else 0)
    else if col v=0 then -RQLift P v (j.val-4)
      else if col v=1 then 0 else RQLift P v (j.val-4)

def RQTripleDet (P : RQConfig) (t : Fin 3 → Fin 9) (q : Fin 3 → ℚ) : ℚ :=
  Matrix.det ![P (t 1)-P (t 0), P (t 2)-P (t 0), q]

def RQQPoly (P : RQConfig) (e : Edge 9) (t t' : Fin 3 → Fin 9) : ℚ :=
  RQTripleDet P t (P e.2-P e.1) * RQTripleDet P t' (P e.1-P (t' 0)) -
    RQTripleDet P t' (P e.2-P e.1) * RQTripleDet P t (P e.1-P (t 0))

def RationalGenericCheck (P : RQConfig) : Prop :=
  (∀ a : Fin 4 → Fin 9, Function.Injective a →
     Matrix.det (fun i j : Fin 4 => RQLift P (a i) j.val) ≠ 0) ∧
  (∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9,
    Function.Injective t → Function.Injective t' →
    Disjoint (Endpoints e) (Finset.univ.image t) →
    Disjoint (Endpoints e) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly P e t t' ≠ 0) ∧
  (∀ col : Fin 9 → ZMod 3,
    (∀ j : ZMod 3, (Finset.univ.filter (fun v => col v=j)).card ≤ 4) →
      (RQSignMatrix P col).det ≠ 0 ∧ ∀ v, LastCofactorQ (RQSignMatrix P col) v ≠ 0)

def WitnessQ : RQConfig := ![![67809,-52884,33379],![-61881,21018,-34390],![-84246,22514,27681],![-73647,-46262,-81810],![22391,-71071,-10109],![96472,89580,-11796],![12046,17632,-15699],![-29491,78050,-20534],![-5281,44075,-22126]]
def WitnessReal : Config 9 3 := fun v j => (WitnessQ v j : ℝ)

def GenericWitnessExact : Prop := RationalGenericCheck WitnessQ

end Sierksma
