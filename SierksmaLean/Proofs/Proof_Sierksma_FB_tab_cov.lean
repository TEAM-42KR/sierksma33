import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
set_option maxRecDepth 200000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

theorem tab_cov_aux : ∀ e0 < 36, ∀ e1 < 36, e0 < e1 → Sierksma.FB.edisj e0 e1 = true →
    ∀ e2 < 36, e1 < e2 → Sierksma.FB.edisj e0 e2 = true → Sierksma.FB.edisj e1 e2 = true →
    ∀ e3 < 36, e2 < e3 → Sierksma.FB.edisj e0 e3 = true → Sierksma.FB.edisj e1 e3 = true →
      Sierksma.FB.edisj e2 e3 = true →
      Sierksma.FB.mRank e0 e1 e2 e3 < 945 ∧ Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 0 = e0 ∧
      Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 1 = e1 ∧
      Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 2 = e2 ∧
      Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 3 = e3 := by
  decide +kernel

theorem proof_Sierksma_FB_tab_cov :
    (∀ i < 1855, ∀ f < 36, ∀ a < 3, Nat.testBit (Sierksma.FB.nt (3 * f + a)) i =
      !Nat.beq (Sierksma.FB.dI i (Sierksma.FB.eu f) (Sierksma.FB.ev f)) a) ∧
    (∀ f < 36, Sierksma.FB.eu f < Sierksma.FB.ev f ∧ Sierksma.FB.ev f < 9) ∧
    (∀ a < 9, ∀ b < 9, a < b → Sierksma.FB.eu (Sierksma.FB.eIdx a b) = a ∧
      Sierksma.FB.ev (Sierksma.FB.eIdx a b) = b ∧ Sierksma.FB.eIdx a b < 36) ∧
    (∀ m < 945, Sierksma.FB.splE m 0 < Sierksma.FB.splE m 1 ∧ Sierksma.FB.splE m 1 < Sierksma.FB.splE m 2 ∧
      Sierksma.FB.splE m 2 < Sierksma.FB.splE m 3 ∧ Sierksma.FB.splE m 3 < 36 ∧
      Sierksma.FB.edisj (Sierksma.FB.splE m 0) (Sierksma.FB.splE m 1) = true ∧
      Sierksma.FB.edisj (Sierksma.FB.splE m 0) (Sierksma.FB.splE m 2) = true ∧
      Sierksma.FB.edisj (Sierksma.FB.splE m 0) (Sierksma.FB.splE m 3) = true ∧
      Sierksma.FB.edisj (Sierksma.FB.splE m 1) (Sierksma.FB.splE m 2) = true ∧
      Sierksma.FB.edisj (Sierksma.FB.splE m 1) (Sierksma.FB.splE m 3) = true ∧
      Sierksma.FB.edisj (Sierksma.FB.splE m 2) (Sierksma.FB.splE m 3) = true) ∧
    (∀ e0 < 36, ∀ e1 < 36, ∀ e2 < 36, ∀ e3 < 36, e0 < e1 → e1 < e2 → e2 < e3 →
      Sierksma.FB.edisj e0 e1 = true → Sierksma.FB.edisj e0 e2 = true → Sierksma.FB.edisj e0 e3 = true →
      Sierksma.FB.edisj e1 e2 = true → Sierksma.FB.edisj e1 e3 = true → Sierksma.FB.edisj e2 e3 = true →
      Sierksma.FB.mRank e0 e1 e2 e3 < 945 ∧ Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 0 = e0 ∧
      Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 1 = e1 ∧
      Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 2 = e2 ∧
      Sierksma.FB.splE (Sierksma.FB.mRank e0 e1 e2 e3) 3 = e3) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro e0 h0 e1 h1 e2 h2 e3 h3 h01 h12 h23 d01 d02 d03 d12 d13 d23
  exact tab_cov_aux e0 h0 e1 h1 h01 d01 e2 h2 h12 d02 d12 e3 h3 h23 d03 d13 d23
