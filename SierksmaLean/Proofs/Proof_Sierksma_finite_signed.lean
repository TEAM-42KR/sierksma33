import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
import SierksmaLean.Theorems.Thm_Sierksma_FB_index_transfer
import SierksmaLean.Theorems.Thm_Sierksma_FB_finite_core
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma

theorem proof_Sierksma_finite_signed (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Universe 3) (hy : SignedSystem y) :
    8 ≤ ((Universe 3).filter (fun Q => y Q ≠ 0)).card := by
  obtain ⟨hc, -, -, -⟩ := Sierksma.FB.index_transfer y hsupp hy
  by_contra h
  exact Sierksma.FB.finite_core y hsupp hy (by omega)
