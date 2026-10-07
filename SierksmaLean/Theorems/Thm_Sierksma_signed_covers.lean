import SierksmaLean.Proofs.Proof_Sierksma_signed_covers
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma

theorem Sierksma.signed_covers :
    ∀ (y : Common.Partition 9 → ZMod 3)
    (hy : SignedSystem y) (g : PairConstraint 9) (hg : ValidConstraint 3 g), ∃ Q ∈ ThreePartitions 9, y Q ≠ 0 ∧ Covers Q g :=
  @proof_Sierksma_signed_covers
