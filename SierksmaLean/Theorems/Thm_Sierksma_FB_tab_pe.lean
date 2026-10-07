import SierksmaLean.Proofs.Proof_Sierksma_FB_tab_pe
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.tab_pe :
    (∀ p < 1855, ∀ f < 37, Sierksma.FB.field (Sierksma.FB.peOf p) f =
      if Nat.testBit (Sierksma.FB.intt f) p then 1 else 0) ∧
    (∀ p < 1855, 9 ≤ ((List.range 36).filter (fun f => Nat.testBit (Sierksma.FB.intt f) p)).length) ∧
    (∀ p < 1855, Nat.testBit (Sierksma.FB.intt 36) p = !Nat.testBit (Sierksma.FB.intt 35) p) ∧
    (∀ f < 37, ∀ p, 1855 ≤ p → Nat.testBit (Sierksma.FB.intt f) p = false) :=
  @proof_Sierksma_FB_tab_pe
