import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
namespace Sierksma
def RelabelConstraint {n : ℕ} (p : Equiv.Perm (Fin n))
    (g : PairConstraint n) : PairConstraint n :=
  let imageEdge : Edge n → Edge n := fun e =>
    (min (p e.1) (p e.2), max (p e.1) (p e.2))
  let imageMatching := g.matching.image imageEdge
  { matching := imageMatching
    twists := fun e =>
      if e ∈ imageMatching then
        let u := p.symm e.1
        let v := p.symm e.2
        if u < v then g.twists (u, v) else -g.twists (v, u)
      else 0 }
end Sierksma

#guard
  let g : Sierksma.PairConstraint 5 :=
    { matching := {(0, 1), (2, 3)}
      twists := fun e => if e = (0, 1) then 1 else 0 }
  let p := Equiv.swap (0 : Fin 5) 1
  let r := Sierksma.RelabelConstraint p g
  r.matching = g.matching ∧ r.twists (0, 1) = 2 ∧
    r.twists (2, 3) = 0 ∧ r.twists (0, 4) = 0 ∧
    Sierksma.RelabelConstraint p r = g
#guard
  let g : Sierksma.PairConstraint 5 :=
    { matching := {(0, 1), (2, 3)}
      twists := fun e => if e = (0, 1) then 1 else 0 }
  let p := Equiv.swap (1 : Fin 5) 4
  let r := Sierksma.RelabelConstraint p g
  r.matching = {(0, 4), (2, 3)} ∧ r.twists (0, 4) = 1 ∧
    r.twists (2, 3) = 0 ∧ r.twists (0, 1) = 0 ∧
    Sierksma.RelabelConstraint p r = g
#guard
  let g : Sierksma.PairConstraint 5 :=
    { matching := {(0, 1), (2, 3)}
      twists := fun e => if e = (0, 1) then 1 else 0 }
  ∀ p : Equiv.Perm (Fin 5),
    let r := Sierksma.RelabelConstraint p g
    r.matching.card = 2 ∧ (r.matching.filter (fun e => r.twists e = 0)).card = 1 ∧
      (∀ e, e ∉ r.matching → r.twists e = 0) ∧
      Sierksma.RelabelConstraint p.symm r = g
