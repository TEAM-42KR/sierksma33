import SierksmaLean.Proofs.Proof_Sierksma_FB_three_partition_colouring
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.three_partition_colouring :
    ∀ (Q : Common.Partition 9) (hQ : Common.IsPartition Q 3), ∃ c : Fin 9 → Fin 3, Function.Surjective c ∧
      Q = (Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun v : Fin 9 => c v = a)) :=
  @proof_Sierksma_FB_three_partition_colouring
