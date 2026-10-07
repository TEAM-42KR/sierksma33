import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_pe
import SierksmaLean.Theorems.Thm_Sierksma_FB_c4lo
set_option autoImplicit false
open Common Sierksma Sierksma.FB
set_option maxRecDepth 10000
set_option maxHeartbeats 600000

theorem proof_Sierksma_FB_sep_profile (S : Finset ℕ) (hS : ∀ i ∈ S, i < 1855) (hcov : coversIdx S) :
    mult S 35 + mult S 36 = S.card ∧ 2 ≤ mult S 36 := by
  classical
  have hcomplement : S.filter (fun i => Nat.testBit (intt 36) i = true) =
      S.filter (fun i => ¬ Nat.testBit (intt 35) i = true) := by
    apply Finset.filter_congr
    intro i hi
    simp only [tab_pe.2.2.1 i (hS i hi), Bool.not_eq_true]
    simp
  have hcard : mult S 35 + mult S 36 = S.card := by
    unfold mult
    rw [hcomplement]
    exact Finset.card_filter_add_card_filter_not (fun i => Nat.testBit (intt 35) i = true)
  refine ⟨hcard, ?_⟩
  have hcoverSep (g : ℕ) (hg : g ∈ c4W) (i : ℕ) (hi : i ∈ S)
      (hc : Nat.testBit (covOf g) i = true) : Nat.testBit (intt 36) i = true := by
    have hz := congrArg (fun n : ℕ => Nat.testBit n i) (c4lo.1 g hg).2
    have hz' : (Nat.testBit (covOf g) i && Nat.testBit (intt 35) i) = false := by
      simpa only [Nat.land_eq, Nat.testBit_land, Nat.zero_testBit] using hz
    have hni : Nat.testBit (intt 35) i = false := by
      simpa only [hc, Bool.true_and] using hz'
    rw [tab_pe.2.2.1 i (hS i hi), hni]
    rfl
  by_contra hn
  have hle : (S.filter (fun i => Nat.testBit (intt 36) i = true)).card ≤ 1 := by
    change mult S 36 ≤ 1
    omega
  have hzero : 0 ∈ c4W := by decide
  obtain ⟨i, hi, hci⟩ := hcov 0 (c4lo.1 0 hzero).1
  have hisep := hcoverSep 0 hzero i hi hci
  obtain ⟨g, hg, hgi⟩ := c4lo.2 i (hS i hi)
  obtain ⟨j, hj, hcj⟩ := hcov g (c4lo.1 g hg).1
  have hjsep := hcoverSep g hg j hj hcj
  have hji : j = i := Finset.card_le_one.mp hle j (Finset.mem_filter.mpr ⟨hj, hjsep⟩)
    i (Finset.mem_filter.mpr ⟨hi, hisep⟩)
  rw [hji, hgi] at hcj
  cases hcj
