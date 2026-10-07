import SierksmaLean.Proofs.Proof_Sierksma_FB_fibre_partition_spec
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.fibre_partition_spec :
    ∀ (c : Fin 9 → Fin 3) (hs : Function.Surjective c), let Q := (Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun v : Fin 9 => c v = a))
    Common.IsPartition Q 3 ∧ ∀ u v : Fin 9, (∃ A ∈ Q, u ∈ A ∧ v ∈ A) ↔ c u = c v :=
  @proof_Sierksma_FB_fibre_partition_spec
