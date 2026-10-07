import SierksmaLean.Proofs.Proof_Sierksma_FB_colour_index_spec
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open scoped BigOperators

theorem Sierksma.FB.colour_index_spec :
    ∀ (c : Fin 9 → Fin 3) (hs : Function.Surjective c)
    (hc : ∀ a : Fin 3, ((Finset.univ : Finset (Fin 9)).filter (fun v => c v = a)).card ≤ 4), let code := ∑ v : Fin 9, (c v).val * 3 ^ v.val
    Sierksma.FB.idxOf code < 1855 ∧ Sierksma.FB.partOf (Sierksma.FB.idxOf code) =
      (Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun v : Fin 9 => c v = a)) :=
  @proof_Sierksma_FB_colour_index_spec
