import SierksmaLean.Proofs.Proof_Sierksma_FB_norm_transport
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.norm_transport :
    ∀ (p : ℕ) (hp : Sierksma.FB.validPerm p = true)
    (ht : ∀ f < 36, Sierksma.FB.tau1 (Sierksma.FB.epOf p f) = Sierksma.FB.tau1 f), (∀ j < 1855, Sierksma.FB.L1t (Sierksma.FB.relIdx p j) = Sierksma.FB.L1t j ∧
      Nat.testBit (Sierksma.FB.intt 36) (Sierksma.FB.relIdx p j) = Nat.testBit (Sierksma.FB.intt 36) j) ∧
    (∀ k < 6, ∀ r < 1855, Sierksma.FB.R1.getD k 0 = r → Sierksma.FB.relIdx p r = r →
      ∀ j < 1855, Sierksma.FB.L2t k (Sierksma.FB.relIdx p j) = Sierksma.FB.L2t k j) ∧
    (∀ S : Finset ℕ, Sierksma.FB.BadY S → Sierksma.FB.BadY (S.image (Sierksma.FB.relIdx p)) ∧
      (S.image (Sierksma.FB.relIdx p)).card = S.card ∧
      Sierksma.FB.mult (S.image (Sierksma.FB.relIdx p)) 36 = Sierksma.FB.mult S 36 ∧
      (∀ f < 36, ∃ g < 36, Sierksma.FB.mult (S.image (Sierksma.FB.relIdx p)) f = Sierksma.FB.mult S g)) :=
  @proof_Sierksma_FB_norm_transport
