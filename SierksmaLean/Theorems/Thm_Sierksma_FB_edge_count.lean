import SierksmaLean.Proofs.Proof_Sierksma_FB_edge_count
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.edge_count :
    ∀ (S : Finset ℕ) (hS : ∀ i ∈ S, i < 1855), 9 * S.card ≤ ∑ f ∈ Finset.range 36, Sierksma.FB.mult S f :=
  @proof_Sierksma_FB_edge_count
