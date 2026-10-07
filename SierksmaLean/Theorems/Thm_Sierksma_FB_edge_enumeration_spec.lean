import SierksmaLean.Proofs.Proof_Sierksma_FB_edge_enumeration_spec
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.edge_enumeration_spec :
    (∀ f < 36, Sierksma.FB.eu f < Sierksma.FB.ev f ∧ Sierksma.FB.ev f < 9 ∧ Sierksma.FB.eIdx (Sierksma.FB.eu f) (Sierksma.FB.ev f) = f) ∧
 (∀ a < 9, ∀ b < 9, a < b → Sierksma.FB.eIdx a b < 36 ∧ Sierksma.FB.eu (Sierksma.FB.eIdx a b) = a ∧ Sierksma.FB.ev (Sierksma.FB.eIdx a b) = b) :=
  @proof_Sierksma_FB_edge_enumeration_spec
