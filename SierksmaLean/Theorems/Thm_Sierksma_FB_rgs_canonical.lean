import SierksmaLean.Proofs.Proof_Sierksma_FB_rgs_canonical
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.rgs_canonical :
    ∀ (c : Fin 9 → Fin 3) (hs : Function.Surjective c)
    (hr : ∀ v : Fin 9, 0 < (c v).val → ∃ w : Fin 9, w < v ∧ (c w).val + 1 = (c v).val), ∀ v : Fin 9, Sierksma.CanonColour
      ((Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun w : Fin 9 => c w = a))) v =
      ((c v).val : ZMod 3) :=
  @proof_Sierksma_FB_rgs_canonical
