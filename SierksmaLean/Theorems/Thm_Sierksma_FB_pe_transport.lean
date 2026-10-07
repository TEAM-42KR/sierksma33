import SierksmaLean.Proofs.Proof_Sierksma_FB_pe_transport
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.pe_transport :
    ∀ (p : ℕ) (hp : Sierksma.FB.validPerm p = true), (∀ f < 36, Sierksma.FB.epOf p f < 36) ∧
    (∀ f < 36, ∀ g < 36, Sierksma.FB.epOf p f = Sierksma.FB.epOf p g → f = g) ∧
    (∀ j < 1855, Sierksma.FB.relIdx p j < 1855) ∧
    (∀ j < 1855, ∀ f < 36, Nat.testBit (Sierksma.FB.intt (Sierksma.FB.epOf p f)) (Sierksma.FB.relIdx p j) = Nat.testBit (Sierksma.FB.intt f) j) :=
  @proof_Sierksma_FB_pe_transport
