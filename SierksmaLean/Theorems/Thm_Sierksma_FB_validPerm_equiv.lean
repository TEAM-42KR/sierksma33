import SierksmaLean.Proofs.Proof_Sierksma_FB_validPerm_equiv
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.validPerm_equiv :
    ∀ (p : ℕ) (hp : Sierksma.FB.validPerm p = true), ∃ π : Equiv.Perm (Fin 9), ∀ v : Fin 9, (π v).val = Sierksma.FB.pAt p v.val :=
  @proof_Sierksma_FB_validPerm_equiv
