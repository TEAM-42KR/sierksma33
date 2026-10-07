import SierksmaLean.Proofs.Proof_Sierksma_FB_norm_sep
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.norm_sep :
    ∀ (S : Finset ℕ) (hS : Sierksma.FB.BadY S) (h2 : 2 ≤ Sierksma.FB.mult S 36), ∃ S' : Finset ℕ, Sierksma.FB.BadY S' ∧ S'.card = S.card ∧ Sierksma.FB.mult S' 36 = Sierksma.FB.mult S 36 ∧
      (∀ f < 36, ∃ g < 36, Sierksma.FB.mult S' f = Sierksma.FB.mult S g) ∧
      ∃ k < 6, ∃ r2 ∈ Sierksma.FB.rootList k, Sierksma.FB.R1.getD k 0 ∈ S' ∧ r2 ∈ S' ∧
        ∀ x ∈ S', x = Sierksma.FB.R1.getD k 0 ∨ x = r2 ∨ Nat.testBit (Sierksma.FB.KS k r2) x = true :=
  @proof_Sierksma_FB_norm_sep
