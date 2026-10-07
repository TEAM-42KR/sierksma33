import SierksmaLean.Proofs.Proof_Sierksma_partition_relabel_inverse_type
import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
open Sierksma

theorem Sierksma.partition_relabel_inverse_type :
    ∀ {n : ℕ}
    (p : Equiv.Perm (Fin n)) (Q : Common.Partition n), Relabel p.symm (Relabel p Q) = Q ∧
      (Relabel p Q).val.map Finset.card = Q.val.map Finset.card :=
  @proof_Sierksma_partition_relabel_inverse_type
