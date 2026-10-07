import SierksmaLean.Proofs.Proof_Sierksma_FB_sep_profile
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false

theorem Sierksma.FB.sep_profile :
    ∀ (S : Finset ℕ) (hS : ∀ i ∈ S, i < 1855) (hcov : Sierksma.FB.coversIdx S), Sierksma.FB.mult S 35 + Sierksma.FB.mult S 36 = S.card ∧ 2 ≤ Sierksma.FB.mult S 36 :=
  @proof_Sierksma_FB_sep_profile
