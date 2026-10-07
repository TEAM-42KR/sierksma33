import SierksmaLean.Proofs.Proof_Sierksma_FB_Kbuild_spec
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false

theorem Sierksma.FB.Kbuild_spec :
    ∀ (P : ℕ → Bool) (x : ℕ), Nat.testBit (Sierksma.FB.Kbuild P) x = (Nat.blt x 1855 && P x) :=
  @proof_Sierksma_FB_Kbuild_spec
