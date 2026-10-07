import SierksmaLean.Proofs.Proof_Sierksma_FB_ternary_code_spec
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open scoped BigOperators

theorem Sierksma.FB.ternary_code_spec :
    ∀ (c : Fin 9 → ℕ) (hc : ∀ v, c v < 3), (∑ v : Fin 9, c v * 3 ^ v.val) < 19683 ∧
    ∀ v : Fin 9, Sierksma.FB.digit3 (∑ w : Fin 9, c w * 3 ^ w.val) v.val = c v :=
  @proof_Sierksma_FB_ternary_code_spec
