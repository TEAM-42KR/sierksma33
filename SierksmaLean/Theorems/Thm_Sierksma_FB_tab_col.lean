import SierksmaLean.Proofs.Proof_Sierksma_FB_tab_col
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.tab_col :
    (∀ i < 1855, Sierksma.FB.colWord i < 262144 ∧ (∀ v < 9, Sierksma.FB.colOf i v < 3) ∧
      Sierksma.FB.colOf i 0 = 0 ∧
      (∀ v < 9, ∀ c < 3, Sierksma.FB.colOf i v = c → 0 < c → ∃ w < v, Sierksma.FB.colOf i w + 1 = c) ∧
      (∀ c < 3, ∃ v < 9, Sierksma.FB.colOf i v = c) ∧
      (∀ c < 3, ((List.range 9).filter (fun v => Nat.beq (Sierksma.FB.colOf i v) c)).length ≤ 4)) ∧
    (∀ i < 1855, Sierksma.FB.idxOf
      (List.foldr (fun v acc => Sierksma.FB.colOf i v * 3 ^ v + acc) 0 (List.range 9)) = i) ∧
    (∀ code < 19683, Sierksma.FB.idxOf code < 1855 → ∀ u < 9, ∀ v < 9,
      (Sierksma.FB.digit3 code u = Sierksma.FB.digit3 code v ↔
        Sierksma.FB.colOf (Sierksma.FB.idxOf code) u = Sierksma.FB.colOf (Sierksma.FB.idxOf code) v)) ∧
    (∀ code < 19683, (∀ c < 3, ∃ v < 9, Sierksma.FB.digit3 code v = c) →
      (∀ c < 3, ((List.range 9).filter (fun v => Nat.beq (Sierksma.FB.digit3 code v) c)).length ≤ 4) →
      Sierksma.FB.idxOf code < 1855) :=
  @proof_Sierksma_FB_tab_col
