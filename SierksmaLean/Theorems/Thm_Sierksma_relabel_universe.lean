import SierksmaLean.Proofs.Proof_Sierksma_relabel_universe
import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
open Sierksma

theorem Sierksma.relabel_universe :
    ∀ (d : ℕ)
    (p : Equiv.Perm (Fin (N d))) (Q : Common.Partition (N d))
    (hQ : Q ∈ Universe d), Relabel p Q ∈ Universe d :=
  @proof_Sierksma_relabel_universe
