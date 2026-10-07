import SierksmaLean.Proofs.Proof_Sierksma_FB_partOf_bij
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.partOf_bij :
    (∀ i < 1855, ∀ j < 1855, Sierksma.FB.partOf i = Sierksma.FB.partOf j → i = j) ∧
    (Finset.range 1855).image Sierksma.FB.partOf = Sierksma.Universe 3 ∧
    (∀ i < 1855, ∀ v : Fin 9,
      Sierksma.CanonColour (Sierksma.FB.partOf i) v = ((Sierksma.FB.colOf i v.val : ℕ) : ZMod 3)) :=
  @proof_Sierksma_FB_partOf_bij
