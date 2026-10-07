import SierksmaLean.Proofs.Proof_Sierksma_FB_max_edge_norm
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false

theorem Sierksma.FB.max_edge_norm :
    ∀ (S : Finset ℕ) (hS : Sierksma.FB.BadY S), ∃ S0 : Finset ℕ, Sierksma.FB.BadY S0 ∧ S0.card = S.card ∧ ∀ f < 36, Sierksma.FB.mult S0 f ≤ Sierksma.FB.mult S0 35 :=
  @proof_Sierksma_FB_max_edge_norm
