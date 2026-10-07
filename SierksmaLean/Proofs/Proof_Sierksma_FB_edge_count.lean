import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_pe
set_option autoImplicit false
open scoped BigOperators
open Sierksma.FB
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem proof_Sierksma_FB_edge_count (S : Finset ℕ) (hS : ∀ i ∈ S, i < 1855) :
    9 * S.card ≤ ∑ f ∈ Finset.range 36, Sierksma.FB.mult S f := by
  classical
  have hrow (i : ℕ) (hi : i ∈ S) :
      9 ≤ ((Finset.range 36).filter (fun f => Nat.testBit (intt f) i = true)).card := by
    have ht := Sierksma.FB.tab_pe.2.1 i (hS i hi)
    have heq : ((List.range 36).filter (fun f => Nat.testBit (intt f) i)).length =
        ((Finset.range 36).filter (fun f => Nat.testBit (intt f) i = true)).card := by
      rw [← List.toFinset_card_of_nodup ((show (List.range 36).Nodup from List.nodup_range).filter _)]
      congr 1
      ext f
      simp
    rw [heq] at ht
    exact ht
  calc
    9 * S.card = ∑ i ∈ S, 9 := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ S, ((Finset.range 36).filter (fun f => Nat.testBit (intt f) i = true)).card :=
      Finset.sum_le_sum hrow
    _ = ∑ f ∈ Finset.range 36, Sierksma.FB.mult S f := by
      simp only [Finset.card_filter, Sierksma.FB.mult]
      exact Finset.sum_comm
