import SierksmaLean.Proofs.Proof_Sierksma_finite_signed
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma

theorem Sierksma.finite_signed :
    ∀ (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Universe 3) (hy : SignedSystem y), 8 ≤ ((Universe 3).filter (fun Q => y Q ≠ 0)).card :=
  @proof_Sierksma_finite_signed
