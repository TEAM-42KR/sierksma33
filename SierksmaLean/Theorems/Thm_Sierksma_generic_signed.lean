import SierksmaLean.Proofs.Proof_Sierksma_generic_signed
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
import SierksmaLean.Definitions.Def_Sierksma_TverbergSign
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma

theorem Sierksma.generic_signed :
    ∃ D : Set (Config 9 3), Dense D ∧
    ∀ P ∈ D, StrongGP P ∧ SignedSystem (TverbergSign P) ∧
      ∀ Q : Common.Partition 9, TverbergSign P Q ≠ 0 ↔ Q ∈ TverbergPartitions 3 P :=
  @proof_Sierksma_generic_signed
