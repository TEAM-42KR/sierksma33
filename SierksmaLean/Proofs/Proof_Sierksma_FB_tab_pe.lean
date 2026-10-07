import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
set_option maxRecDepth 200000

theorem proof_Sierksma_FB_tab_pe :
    (∀ p < 1855, ∀ f < 37, Sierksma.FB.field (Sierksma.FB.peOf p) f =
      if Nat.testBit (Sierksma.FB.intt f) p then 1 else 0) ∧
    (∀ p < 1855, 9 ≤ ((List.range 36).filter (fun f => Nat.testBit (Sierksma.FB.intt f) p)).length) ∧
    (∀ p < 1855, Nat.testBit (Sierksma.FB.intt 36) p = !Nat.testBit (Sierksma.FB.intt 35) p) ∧
    (∀ f < 37, ∀ p, 1855 ≤ p → Nat.testBit (Sierksma.FB.intt f) p = false) := by
  have hlt : ∀ f < 37, Sierksma.FB.intt f < 2 ^ 1855 := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro f hf p hp
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hlt f hf) (Nat.pow_le_pow_right (by norm_num) hp))
