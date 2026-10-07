import SierksmaLean.Proofs.Proof_Sierksma_FB_nine_list_bridge
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open scoped BigOperators

theorem Sierksma.FB.nine_list_bridge :
    ∀ (c : ℕ → ℕ), List.foldr (fun v acc => c v * 3 ^ v + acc) 0 (List.range 9) = (∑ v : Fin 9, c v.val * 3 ^ v.val) ∧
    ∀ a : ℕ, ((List.range 9).filter (fun v => Nat.beq (c v) a)).length =
      ((Finset.univ : Finset (Fin 9)).filter (fun v => c v.val = a)).card :=
  @proof_Sierksma_FB_nine_list_bridge
