import SierksmaLean.Theorems.Thm_Sierksma_FB_index_transfer
import SierksmaLean.Theorems.Thm_Sierksma_FB_relabel_idx
import SierksmaLean.Theorems.Thm_Sierksma_FB_relIdx_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_edge_count
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_pe
import SierksmaLean.Theorems.Thm_Sierksma_FB_pe_transport
import SierksmaLean.Theorems.Thm_Sierksma_FB_norm_sep
import SierksmaLean.Theorems.Thm_Sierksma_FB_famC4
import SierksmaLean.Theorems.Thm_Sierksma_FB_famA
import SierksmaLean.Theorems.Thm_Sierksma_FB_famB
import SierksmaLean.Theorems.Thm_Sierksma_FB_enormtab
import SierksmaLean.Theorems.Thm_Sierksma_FB_c4lo
import SierksmaLean.Theorems.Thm_Sierksma_FB_max_edge_norm
import SierksmaLean.Theorems.Thm_Sierksma_FB_sep_profile
import SierksmaLean.Theorems.Thm_Sierksma_FB_finite_core_box_aux
set_option autoImplicit false
open Common Sierksma Sierksma.FB
set_option maxRecDepth 10000
set_option maxHeartbeats 600000

theorem proof_Sierksma_FB_finite_core (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Sierksma.Universe 3) (hy : Sierksma.SignedSystem y)
    (hcard : (Sierksma.FB.idxSupp y).card ≤ 7) : False := by
  classical
  let S := idxSupp y
  have hBad : BadY S := ⟨y, hsupp, hy, rfl⟩
  obtain ⟨S0, hBad0, hCard0, hMax0⟩ := max_edge_norm S hBad
  have hCard0le : S0.card ≤ 7 := by simpa only [hCard0] using hcard
  obtain ⟨y0, hsupp0, hy0, hidx0⟩ := hBad0
  have hBad0 : BadY S0 := ⟨y0, hsupp0, hy0, hidx0⟩
  have hTransfer0 := index_transfer y0 hsupp0 hy0
  have hBound0 : ∀ i ∈ S0, i < 1855 := by rw [← hidx0]; exact hTransfer0.2.1
  have hCov0 : coversIdx S0 := by rw [← hidx0]; exact hTransfer0.2.2.2
  have hProfile := sep_profile S0 hBound0 hCov0
  have hTwo : 2 ≤ mult S0 36 := hProfile.2
  have exclude (e s : ℕ)
      (hfields : ∀ f < 36, field (capsOf e s) f = e)
      (hsepfield : field (capsOf e s) 36 = s)
      (he : ∀ f < 36, mult S0 f ≤ e) (hs : mult S0 36 ≤ s)
      (hcert : ∀ k < 6, ∀ r2 ∈ rootList k,
        Good (memBits (pairSort (R1.getD k 0) r2)) (KS k r2) 5 (capsOf e s)) : False := by
    obtain ⟨S', hBad', hCard', hSep', hTrans', k, hk, r2, hr2, hr1mem, hr2mem, hbox⟩ :=
      norm_sep S0 hBad0 hTwo
    let r1 := R1.getD k 0
    let C := memBits (pairSort r1 r2)
    have hne : r1 ≠ r2 := finite_core_box_aux.2.1 k hk r2 hr2
    have hpair : ∀ i, Nat.testBit C i = true ↔ i = r1 ∨ i = r2 :=
      finite_core_box_aux.1 r1 r2
    have hC : ∀ i, Nat.testBit C i = true → i ∈ S' := by
      intro i hi
      rcases (hpair i).mp hi with h | h
      · simpa only [h] using hr1mem
      · simpa only [h] using hr2mem
    have hCK : ∀ i ∈ S', Nat.testBit C i = true ∨ Nat.testBit (KS k r2) i = true := by
      intro i hi
      rcases hbox i hi with h | h | h
      · exact Or.inl ((hpair i).mpr (Or.inl h))
      · exact Or.inl ((hpair i).mpr (Or.inr h))
      · exact Or.inr h
    have hPairFilter : S'.filter (fun i => Nat.testBit C i = true) = {r1, r2} := by
      ext i
      constructor
      · intro hi
        simpa only [Finset.mem_insert, Finset.mem_singleton] using (hpair i).mp (Finset.mem_filter.mp hi).2
      · intro hi
        have hip : i = r1 ∨ i = r2 := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
        have hib : Nat.testBit C i = true := (hpair i).mpr hip
        exact Finset.mem_filter.mpr ⟨hC i hib, hib⟩
    have hPairCard : (S'.filter (fun i => Nat.testBit C i = true)).card = 2 := by
      rw [hPairFilter]
      simp [hne]
    have hFalseFilter : S'.filter (fun i => Nat.testBit C i = false) =
        S'.filter (fun i => ¬ Nat.testBit C i = true) := by
      apply Finset.filter_congr
      intro i _
      cases Nat.testBit C i <;> simp
    have hCount := Finset.card_filter_add_card_filter_not (s := S') (fun i => Nat.testBit C i = true)
    rw [hPairCard, ← hFalseFilter] at hCount
    have hBudget : (S'.filter (fun i => Nat.testBit C i = false)).card ≤ 5 := by
      omega
    have hCap : capOK S' (capsOf e s) := by
      intro f hf
      by_cases hf36 : f < 36
      · obtain ⟨g, hg, hfg⟩ := hTrans' f hf36
        rw [hfields f hf36, hfg]
        exact he g hg
      · have hf36eq : f = 36 := by omega
        subst f
        rw [hsepfield, hSep']
        exact hs
    obtain ⟨y', hsupp', hy', hidx'⟩ := hBad'
    have hTransfer' := index_transfer y' hsupp' hy'
    have hCov' : coversIdx S' := by rw [← hidx']; exact hTransfer'.2.2.2
    have hSigned' : signedIdx S' := by rw [← hidx']; exact hTransfer'.2.2.1
    exact hcert k hk r2 hr2 S' hC hCK hBudget hCap hCov' hSigned'
  by_cases hsmall : mult S0 36 ≤ 3
  · have he : ∀ f < 36, mult S0 f ≤ 15 := by
      intro f hf
      have hm := hMax0 f hf
      omega
    exact exclude 15 3 finite_core_box_aux.2.2.1.1 finite_core_box_aux.2.2.1.2 he hsmall famC4
  · have hSep4 : 4 ≤ mult S0 36 := by omega
    have hsumUpper : (∑ f ∈ Finset.range 36, mult S0 f) ≤ 36 * mult S0 35 := by
      calc
        (∑ f ∈ Finset.range 36, mult S0 f) ≤ ∑ f ∈ Finset.range 36, mult S0 35 := by
          apply Finset.sum_le_sum
          intro f hf
          exact hMax0 f (Finset.mem_range.mp hf)
        _ = 36 * mult S0 35 := by simp
    have hsumLower := edge_count S0 hBound0
    have hM : mult S0 35 = 3 ∨ mult S0 35 = 2 := by omega
    rcases hM with hm | hm
    · have he : ∀ f < 36, mult S0 f ≤ 3 := by
        intro f hf
        simpa only [hm] using hMax0 f hf
      have hs : mult S0 36 ≤ 4 := by omega
      exact exclude 3 4 finite_core_box_aux.2.2.2.1.1 finite_core_box_aux.2.2.2.1.2 he hs famA
    · have he : ∀ f < 36, mult S0 f ≤ 2 := by
        intro f hf
        simpa only [hm] using hMax0 f hf
      have hs : mult S0 36 ≤ 5 := by omega
      exact exclude 2 5 finite_core_box_aux.2.2.2.2.1 finite_core_box_aux.2.2.2.2.2 he hs famB
