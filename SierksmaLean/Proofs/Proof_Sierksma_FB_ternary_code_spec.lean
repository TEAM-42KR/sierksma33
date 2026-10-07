import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open scoped BigOperators
open Sierksma.FB
set_option maxHeartbeats 800000

theorem proof_Sierksma_FB_ternary_code_spec (c : Fin 9 → ℕ) (hc : ∀ v, c v < 3) :
    (∑ v : Fin 9, c v * 3 ^ v.val) < 19683 ∧
    ∀ v : Fin 9, digit3 (∑ w : Fin 9, c w * 3 ^ w.val) v.val = c v := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  have h7 := hc 7
  have h8 := hc 8
  have hs : (∑ v : Fin 9, c v * 3 ^ v.val) = c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561 := by
    simp [Fin.sum_univ_succ, Fin.succ]
    <;> omega
  rw [hs]
  constructor
  · omega
  · intro v
    fin_cases v
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 1 % 3 = c 0
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 3 % 3 = c 1
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 9 % 3 = c 2
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 27 % 3 = c 3
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 81 % 3 = c 4
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 243 % 3 = c 5
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 729 % 3 = c 6
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 2187 % 3 = c 7
      omega
    · change (c 0 * 1 + c 1 * 3 + c 2 * 9 + c 3 * 27 + c 4 * 81 + c 5 * 243 + c 6 * 729 + c 7 * 2187 + c 8 * 6561) / 6561 % 3 = c 8
      omega
