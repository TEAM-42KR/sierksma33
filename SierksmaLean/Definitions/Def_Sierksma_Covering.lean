import SierksmaLean.Definitions.Def_Common_TverbergPartitions
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Common
namespace Sierksma
abbrev N (d : ℕ) := 2*d+3
abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev Family (n : ℕ) := Finset (Common.Partition n)
def Endpoints {n : ℕ} (e : Edge n) : Block n := {e.1,e.2}
def IsMatching {n : ℕ} (M : Finset (Edge n)) : Prop :=
 (∀ e ∈ M, e.1 < e.2) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (Endpoints e) (Endpoints f)
def Internal {n : ℕ} (Q : Common.Partition n) (e : Edge n) : Prop := ∃ A ∈ Q, e.1 ∈ A ∧ e.2 ∈ A
def Avoids {n : ℕ} (Q : Common.Partition n) (M : Finset (Edge n)) : Prop := ∀ e ∈ M, ¬ Internal Q e
def AtMostThree {n : ℕ} (Q : Common.Partition n) : Prop := BlocksOn Q Finset.univ ∧ Q.card ≤ 3
def MatchingCover {n : ℕ} (F : Family n) : Prop :=
 (∀ Q ∈ F, AtMostThree Q) ∧ ∀ M : Finset (Edge n), IsMatching M → ∃ Q ∈ F, Avoids Q M
def MatchingNumber (n : ℕ) : ℕ := sInf {k | ∃ F : Family n, MatchingCover F ∧ F.card = k}
def Universe (d : ℕ) : Family (N d) := by
 classical
 exact Finset.univ.filter (fun Q => IsPartition Q 3 ∧ ∀ A ∈ Q, A.card ≤ d+1)
structure PairConstraint (n : ℕ) where
 matching : Finset (Edge n)
 twists : Edge n → ZMod 3
 deriving DecidableEq, Fintype
def ValidConstraint (d : ℕ) (g : PairConstraint (N d)) : Prop :=
 IsMatching g.matching ∧ g.matching.card = d+1 ∧ ∀ e, e ∉ g.matching → g.twists e = 0
def Constraints (d : ℕ) : Finset (PairConstraint (N d)) := by
 classical
 exact Finset.univ.filter (ValidConstraint d)
def Respects {n : ℕ} (Q : Common.Partition n) (col : Fin n → ZMod 3) : Prop :=
 ∀ u v, col u = col v ↔ ∃ A ∈ Q, u ∈ A ∧ v ∈ A
def Covers {n : ℕ} (Q : Common.Partition n) (g : PairConstraint n) : Prop :=
 ∃ col : Fin n → ZMod 3, Respects Q col ∧ ∀ e ∈ g.matching, col e.2 - col e.1 ≠ g.twists e
def Covering (d : ℕ) (F : Family (N d)) : Prop :=
 F ⊆ Universe d ∧ ∀ g, ValidConstraint d g → ∃ Q ∈ F, Covers Q g
def BirchEven {n : ℕ} (F : Family n) : Prop := by
 classical
 exact ∀ v : Fin n, Even ((F.filter (fun Q => ({v} : Block n) ∈ Q)).card)
def Beta (d : ℕ) : ℕ := sInf {k | ∃ F : Family (N d), Covering d F ∧ F.card = k}
def BetaEven : ℕ := sInf {k | ∃ F : Family 9, Covering 3 F ∧ BirchEven F ∧ F.card = k}
def Multiplicity {n : ℕ} (F : Family n) (e : Edge n) : ℕ := by
 classical
 exact (F.filter (fun Q => Internal Q e)).card
def Relabel {n : ℕ} (p : Equiv.Perm (Fin n)) (Q : Common.Partition n) : Common.Partition n := Q.image (fun A => A.image p)
def RelabelFamily {n : ℕ} (p : Equiv.Perm (Fin n)) (F : Family n) : Family n := F.image (Relabel p)
def SameOrbit {n : ℕ} (F G : Family n) : Prop := ∃ p : Equiv.Perm (Fin n), RelabelFamily p F = G
def SevenCovers : Finset (Family 9) := by
 classical
 exact (Universe 3).powerset.filter (fun F => F.card = 7 ∧ MatchingCover F)
def SeedCovers : Finset (Family 7) := by
 classical
 exact Finset.univ.filter (fun F : Family 7 => F.card = 4 ∧ MatchingCover F)
def InternalCount {n : ℕ} (Q : Common.Partition n) : ℕ := by
 classical
 exact (Finset.univ.filter (fun e : Edge n => e.1 < e.2 ∧ Internal Q e)).card
def BinaryPoint (x : Fin 9) : Fin 3 → ZMod 2 := fun i => ((x.val / 2^i.val) % 2 : ℕ)
def BinaryCut (a : Fin 3 → ZMod 2) : Common.Partition 9 := by
 classical
 exact { {8}, Finset.univ.filter (fun x => x.val < 8 ∧ ∑ i, a i * BinaryPoint x i = 0),
 Finset.univ.filter (fun x => x.val < 8 ∧ ∑ i, a i * BinaryPoint x i = 1) }
def F7 : Family 9 := by
 classical
 exact (Finset.univ.filter (fun a : Fin 3 → ZMod 2 => a ≠ 0)).image BinaryCut
def ClusterPairs (d : ℕ) : Finset (Edge (N d)) :=
 Finset.univ.filter (fun e => e.1.val % 2 = 1 ∧ e.2.val = e.1.val+1)
def ClusterFamily (d : ℕ) : Family (N d) := by
 classical
 exact (Universe d).filter (fun Q => ({0} : Block (N d)) ∈ Q ∧ Avoids Q (ClusterPairs d))
def CommonCrossGraph {n : ℕ} (F : Family n) (u v : Fin n) : Prop := u ≠ v ∧ ∀ Q ∈ F, ¬ Internal Q (u,v)
def Restricted {n : ℕ} (Q : Common.Partition n) (Y : Block n) : Common.Partition n :=
 (Q.image (fun A => A ∩ Y)).erase ∅
def CoversOn {n : ℕ} (F : Family n) (Y : Block n) : Prop :=
 (∀ Q ∈ F, BlocksOn Q Y ∧ Q.card ≤ 3) ∧ ∀ M : Finset (Edge n), IsMatching M →
 (∀ e ∈ M, e.1 ∈ Y ∧ e.2 ∈ Y) → ∃ Q ∈ F, Avoids Q M
def SurvivingRestriction {n : ℕ} (F : Family n) (M : Finset (Edge n)) : Family n := by
 classical
 exact (F.filter (fun Q => Avoids Q M)).image (fun Q => Restricted Q (Finset.univ \ M.biUnion Endpoints))
def Select {α : Type*} [DecidableEq α] (pred : α → Prop) (xs : Finset α) : Finset α := by
 classical
 exact xs.filter pred
def G7 : Family 9 := {
 {{7,8},{4,5,6},{0,1,2,3}},
 {{5,6},{0,1,7},{2,3,4,8}}, {{5,6},{2,3,7},{0,1,4,8}},
 {{4,6},{0,2,7},{1,3,5,8}}, {{4,6},{1,3,7},{0,2,5,8}},
 {{4,5},{0,3,7},{1,2,6,8}}, {{4,5},{1,2,7},{0,3,6,8}} }
end Sierksma
