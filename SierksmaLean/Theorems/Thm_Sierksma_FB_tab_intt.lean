import SierksmaLean.Proofs.Proof_Sierksma_FB_tab_intt
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.tab_intt :
    ∀ i < 1855, ∀ f < 36,
    Nat.testBit (Sierksma.FB.intt f) i = Nat.beq (Sierksma.FB.colOf i (Sierksma.FB.eu f)) (Sierksma.FB.colOf i (Sierksma.FB.ev f)) :=
  @proof_Sierksma_FB_tab_intt
