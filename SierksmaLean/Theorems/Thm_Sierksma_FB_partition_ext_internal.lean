import SierksmaLean.Proofs.Proof_Sierksma_FB_partition_ext_internal
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.partition_ext_internal :
    ∀ (Q R : Common.Partition 9)
    (hQ : Common.IsPartition Q 3) (hR : Common.IsPartition R 3)
    (h : ∀ u v : Fin 9, (∃ A ∈ Q, u ∈ A ∧ v ∈ A) ↔ (∃ A ∈ R, u ∈ A ∧ v ∈ A)), Q = R :=
  @proof_Sierksma_FB_partition_ext_internal
