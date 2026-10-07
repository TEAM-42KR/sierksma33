import SierksmaLean.Proofs.Proof_Sierksma_FB_relIdx_spec
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.relIdx_spec :
    ∀ (π : Equiv.Perm (Fin 9)) (p : ℕ)
    (hp : ∀ v : Fin 9, (π v).val = Sierksma.FB.pAt p v.val), (∀ i < 1855, Sierksma.FB.relIdx p i < 1855 ∧
      Sierksma.FB.partOf (Sierksma.FB.relIdx p i) = Sierksma.Relabel π (Sierksma.FB.partOf i)) ∧
    (∀ i < 1855, ∀ j < 1855, Sierksma.FB.relIdx p i = Sierksma.FB.relIdx p j → i = j) :=
  @proof_Sierksma_FB_relIdx_spec
