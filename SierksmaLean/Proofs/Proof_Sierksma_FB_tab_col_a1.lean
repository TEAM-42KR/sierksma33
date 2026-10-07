import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
set_option maxRecDepth 200000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

theorem proof_Sierksma_FB_tab_col_a1 :
    ∀ i < 1855, 464 ≤ i → i < 928 → Sierksma.FB.colWord i < 262144 ∧ (∀ v < 9, Sierksma.FB.colOf i v < 3) ∧
      Sierksma.FB.colOf i 0 = 0 ∧
      (∀ v < 9, ∀ c < 3, Sierksma.FB.colOf i v = c → 0 < c → ∃ w < v, Sierksma.FB.colOf i w + 1 = c) ∧
      (∀ c < 3, ∃ v < 9, Sierksma.FB.colOf i v = c) ∧
      (∀ c < 3, ((List.range 9).filter (fun v => Nat.beq (Sierksma.FB.colOf i v) c)).length ≤ 4) := by
  decide +kernel
