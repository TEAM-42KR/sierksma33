import SierksmaLean.Proofs.Proof_Sierksma_FB_sharedBlock_relabel
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.sharedBlock_relabel :
    ∀ (π : Equiv.Perm (Fin 9)) (Q : Common.Partition 9) (u v : Fin 9), (∃ A ∈ Sierksma.Relabel π Q, π u ∈ A ∧ π v ∈ A) ↔ (∃ A ∈ Q, u ∈ A ∧ v ∈ A) :=
  @proof_Sierksma_FB_sharedBlock_relabel
