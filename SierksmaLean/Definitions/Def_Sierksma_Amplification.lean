import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Sierksma
def M (n k : ℕ) : ℕ := n.factorial / ((n-2*k).factorial * 2^k * k.factorial)
def HTriple (a b c k : ℕ) : ℕ := ∑ z ∈ Finset.range (k+1),
 (a.descFactorial z * b.descFactorial z / z.factorial) * (a+b-2*z).choose (k-z) * c.descFactorial (k-z)
def H (n k : ℕ) : ℕ := HTriple (n/3) ((n+1)/3) ((n+2)/3) k
def CeilRatio (a b : ℕ) : ℕ := (a+b-1)/b
def Amplification (seed : ℕ → ℕ) : ℕ → ℕ
 | 0 => 0
 | 1 => 0
 | d+2 => max (seed (d+2)) (((Finset.range (d+2)).attach).sup (fun h =>
    CeilRatio (Amplification seed h.val * M (N (d+2)) (d+2-h.val)) (H (N (d+2)) (d+2-h.val))))
termination_by d => d
decreasing_by
 have hh := Finset.mem_range.mp h.property
 omega
def F (d : ℕ) : ℕ := Amplification (fun h => if h=2 then 4 else 0) d
def C (d : ℕ) : ℕ := Amplification (fun h => if h=2 then 4 else if h=3 then 7 else 0) d
def B : ℕ → ℕ
 | 0 => 0
 | 1 => 0
 | 2 => 4
 | d+3 => CeilRatio ((N (d+3)).choose 2 * B (d+2)) ((N (d+3))^2/3)
def G (d : ℕ) : ℕ := CeilRatio (4*M (N d) (d-2)) (H (N d) (d-2))
def R (d : ℕ) : ℕ := CeilRatio (7*M (N d) (d-3)) (H (N d) (d-3))
def VZ (d : ℕ) : ℝ := (1/2) * (3/2 : ℝ)^(d+1)
end Sierksma
