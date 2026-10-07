import SierksmaLean.Proofs.Proof_Sierksma_count_lower_of_dense
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
set_option autoImplicit false
open scoped BigOperators
open Common

theorem Sierksma.count_lower_of_dense :
    ∀ (D : Set (Config 9 3)) (hD : Dense D) (k : ℕ)
    (hk : ∀ P ∈ D, k ≤ TverbergCount 3 P) (P : Config 9 3), k ≤ TverbergCount 3 P :=
  @proof_Sierksma_count_lower_of_dense
