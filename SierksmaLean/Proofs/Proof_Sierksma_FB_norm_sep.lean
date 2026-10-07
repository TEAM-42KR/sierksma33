import SierksmaLean.Theorems.Thm_Sierksma_FB_norm_transport
import SierksmaLean.Theorems.Thm_Sierksma_FB_normtab1
import SierksmaLean.Theorems.Thm_Sierksma_FB_normtab2
import SierksmaLean.Theorems.Thm_Sierksma_FB_Kbuild_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_validPerm_equiv
import SierksmaLean.Theorems.Thm_Sierksma_FB_relIdx_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_index_transfer
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem proof_Sierksma_FB_norm_sep (S : Finset ℕ) (hS : Sierksma.FB.BadY S) (h2 : 2 ≤ Sierksma.FB.mult S 36) :
    ∃ S' : Finset ℕ, Sierksma.FB.BadY S' ∧ S'.card = S.card ∧ Sierksma.FB.mult S' 36 = Sierksma.FB.mult S 36 ∧
      (∀ f < 36, ∃ g < 36, Sierksma.FB.mult S' f = Sierksma.FB.mult S g) ∧
      ∃ k < 6, ∃ r2 ∈ Sierksma.FB.rootList k, Sierksma.FB.R1.getD k 0 ∈ S' ∧ r2 ∈ S' ∧
        ∀ x ∈ S', x = Sierksma.FB.R1.getD k 0 ∨ x = r2 ∨ Nat.testBit (Sierksma.FB.KS k r2) x = true := by
  classical
  have hbound (T : Finset ℕ) (hT : BadY T) (x : ℕ) (hx : x ∈ T) : x < 1855 := by
    obtain ⟨y,hy,hs,hyi⟩ := hT
    rw [← hyi] at hx
    exact (index_transfer y hy hs).2.1 x hx
  have hinjective (p : ℕ) (hp : validPerm p = true) (T : Finset ℕ) (hT : BadY T) :
      Set.InjOn (relIdx p) (↑T : Set ℕ) := by
    obtain ⟨π,hπ⟩ := validPerm_equiv p hp
    intro i hi j hj heq
    exact (relIdx_spec π p hπ).2 i (hbound T hT i hi) j (hbound T hT j hj) heq
  let A := S.filter (fun x => Nat.testBit (intt 36) x = true)
  have hAc : 2 ≤ A.card := h2
  have hAn : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r,hrA,hmin⟩ := Finset.exists_min_image A L1t hAn
  have hrS : r ∈ S := (Finset.mem_filter.mp hrA).1
  have hrs : Nat.testBit (intt 36) r = true := (Finset.mem_filter.mp hrA).2
  have hrb := hbound S hS r hrS
  obtain ⟨hp1,ht1,k,hk,hroot⟩ := normtab1 r hrb hrs
  let p1 := n1 r
  let r1 := R1.getD k 0
  let S1 := S.image (relIdx p1)
  have hn1 := norm_transport p1 hp1 ht1
  have htr1 := hn1.2.2 S hS
  have hS1 : BadY S1 := htr1.1
  have hc1 : S1.card = S.card := htr1.2.1
  have hm1 : mult S1 36 = mult S 36 := htr1.2.2.1
  have hr1S : r1 ∈ S1 := by
    exact Finset.mem_image.mpr ⟨r,hrS,hroot⟩
  have hr1b : r1 < 1855 := hbound S1 hS1 r1 hr1S
  have hr1s : Nat.testBit (intt 36) r1 = true := by
    have hh := (hn1.1 r hrb).2
    rw [hroot] at hh
    exact hh.trans hrs
  have hmin1 (x : ℕ) (hx : x ∈ S1) (hs : Nat.testBit (intt 36) x = true) : L1t r1 ≤ L1t x := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    have hjb := hbound S hS j hj
    have hjs : Nat.testBit (intt 36) j = true := by
      rw [← (hn1.1 j hjb).2]
      exact hs
    have hle := hmin j (Finset.mem_filter.mpr ⟨hj,hjs⟩)
    have hrootlab : L1t r1 = L1t r := by
      have heq : relIdx p1 r = r1 := hroot
      rw [← heq]
      exact (hn1.1 r hrb).1
    rw [hrootlab,(hn1.1 j hjb).1]
    exact hle
  let A1 := S1.filter (fun x => Nat.testBit (intt 36) x = true)
  have hr1A : r1 ∈ A1 := Finset.mem_filter.mpr ⟨hr1S,hr1s⟩
  have hA1c : 2 ≤ A1.card := by
    change 2 ≤ mult S1 36
    rw [hm1]
    exact h2
  have hA1n : (A1.erase r1).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hr1A]
    omega
  obtain ⟨t,htA,hmin2⟩ := Finset.exists_min_image (A1.erase r1) (L2t k) hA1n
  have htn : t ≠ r1 := (Finset.mem_erase.mp htA).1
  have htS : t ∈ S1 := (Finset.mem_filter.mp (Finset.mem_erase.mp htA).2).1
  have hts : Nat.testBit (intt 36) t = true := (Finset.mem_filter.mp (Finset.mem_erase.mp htA).2).2
  have htb := hbound S1 hS1 t htS
  obtain ⟨hp2,ht2,hfix,hroot2⟩ := normtab2 k hk t htb hts htn (hmin1 t htS hts)
  let p2 := n2 k t
  let r2 := relIdx p2 t
  let S2 := S1.image (relIdx p2)
  have hn2 := norm_transport p2 hp2 ht2
  have htr2 := hn2.2.2 S1 hS1
  have hS2 : BadY S2 := htr2.1
  have hc2 : S2.card = S1.card := htr2.2.1
  have hm2 : mult S2 36 = mult S1 36 := htr2.2.2.1
  have hr1S2 : r1 ∈ S2 := Finset.mem_image.mpr ⟨r1,hr1S,hfix⟩
  have hr2S2 : r2 ∈ S2 := Finset.mem_image.mpr ⟨t,htS,rfl⟩
  have hL2 := hn2.2.1 k hk r1 hr1b rfl hfix
  have hmin1' (x : ℕ) (hx : x ∈ S2) (hs : Nat.testBit (intt 36) x = true) : L1t r1 ≤ L1t x := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    have hjb := hbound S1 hS1 j hj
    have hjs : Nat.testBit (intt 36) j = true := by
      rw [← (hn2.1 j hjb).2]
      exact hs
    rw [(hn2.1 j hjb).1]
    exact hmin1 j hj hjs
  have hmin2' (x : ℕ) (hx : x ∈ S2) (hs : Nat.testBit (intt 36) x = true)
      (hx1 : x ≠ r1) : L2t k r2 ≤ L2t k x := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    have hjb := hbound S1 hS1 j hj
    have hjs : Nat.testBit (intt 36) j = true := by
      rw [← (hn2.1 j hjb).2]
      exact hs
    have hjn : j ≠ r1 := by
      intro h
      apply hx1
      rw [h]
      exact hfix
    have hjA : j ∈ A1.erase r1 := Finset.mem_erase.mpr ⟨hjn,Finset.mem_filter.mpr ⟨hj,hjs⟩⟩
    change L2t k (relIdx p2 t) ≤ L2t k (relIdx p2 j)
    rw [hL2 t htb,hL2 j hjb]
    exact hmin2 j hjA
  refine ⟨S2,hS2,hc2.trans hc1,hm2.trans hm1,?_,k,hk,r2,hroot2,hr1S2,hr2S2,?_⟩
  · intro f hf
    obtain ⟨g,hg,hfg⟩ := htr2.2.2.2 f hf
    obtain ⟨g',hg',hgg'⟩ := htr1.2.2.2 g hg
    exact ⟨g',hg',hfg.trans hgg'⟩
  · intro x hx
    by_cases hx1 : x = r1
    · exact Or.inl hx1
    by_cases hx2 : x = r2
    · exact Or.inr (Or.inl hx2)
    apply Or.inr ∘ Or.inr
    change Nat.testBit (Kbuild (kpred k r2)) x = true
    rw [Kbuild_spec,Bool.and_eq_true_iff]
    refine ⟨by simpa using hbound S2 hS2 x hx,?_⟩
    have hbx1 : Nat.beq x r1 = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      exact hx1 (Nat.eq_of_beq_eq_true he)
    have hbx2 : Nat.beq x r2 = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      exact hx2 (Nat.eq_of_beq_eq_true he)
    change (!(Nat.beq x r1) && !(Nat.beq x r2) &&
      (!(Nat.testBit (intt 36) x) || (Nat.ble (L1t r1) (L1t x) && Nat.ble (L2t k r2) (L2t k x)))) = true
    simp only [hbx1,hbx2,Bool.not_false,Bool.true_and]
    by_cases hs : Nat.testBit (intt 36) x = true
    · rw [hs,Bool.not_true,Bool.false_or,Bool.and_eq_true_iff]
      exact ⟨by simpa using hmin1' x hx hs,by simpa using hmin2' x hx hs hx1⟩
    · have hsf : Nat.testBit (intt 36) x = false := Bool.eq_false_iff.mpr hs
      simp only [hsf,Bool.not_false,Bool.true_or]

