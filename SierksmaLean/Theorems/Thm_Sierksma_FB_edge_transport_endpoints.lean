import SierksmaLean.Proofs.Proof_Sierksma_FB_edge_transport_endpoints
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.edge_transport_endpoints :
    ∀ (p : ℕ) (π : Equiv.Perm (Fin 9)) (hπ : ∀ v : Fin 9, (π v).val = Sierksma.FB.pAt p v.val), ∀ f < 36, Sierksma.FB.epOf p f < 36 ∧
 ((Sierksma.FB.eu (Sierksma.FB.epOf p f) = Sierksma.FB.pAt p (Sierksma.FB.eu f) ∧ Sierksma.FB.ev (Sierksma.FB.epOf p f) = Sierksma.FB.pAt p (Sierksma.FB.ev f)) ∨
  (Sierksma.FB.eu (Sierksma.FB.epOf p f) = Sierksma.FB.pAt p (Sierksma.FB.ev f) ∧ Sierksma.FB.ev (Sierksma.FB.epOf p f) = Sierksma.FB.pAt p (Sierksma.FB.eu f))) :=
  @proof_Sierksma_FB_edge_transport_endpoints
