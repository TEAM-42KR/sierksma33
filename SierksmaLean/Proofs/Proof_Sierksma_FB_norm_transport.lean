import SierksmaLean.Theorems.Thm_Sierksma_FB_pe_transport
import SierksmaLean.Theorems.Thm_Sierksma_FB_labtab
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_pe
import SierksmaLean.Theorems.Thm_Sierksma_FB_validPerm_equiv
import SierksmaLean.Theorems.Thm_Sierksma_FB_relIdx_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_relabel_idx
import SierksmaLean.Theorems.Thm_Sierksma_FB_index_transfer
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem proof_Sierksma_FB_norm_transport (p : ℕ) (hp : Sierksma.FB.validPerm p = true)
    (ht : ∀ f < 36, Sierksma.FB.tau1 (Sierksma.FB.epOf p f) = Sierksma.FB.tau1 f) :
    (∀ j < 1855, Sierksma.FB.L1t (Sierksma.FB.relIdx p j) = Sierksma.FB.L1t j ∧
      Nat.testBit (Sierksma.FB.intt 36) (Sierksma.FB.relIdx p j) = Nat.testBit (Sierksma.FB.intt 36) j) ∧
    (∀ k < 6, ∀ r < 1855, Sierksma.FB.R1.getD k 0 = r → Sierksma.FB.relIdx p r = r →
      ∀ j < 1855, Sierksma.FB.L2t k (Sierksma.FB.relIdx p j) = Sierksma.FB.L2t k j) ∧
    (∀ S : Finset ℕ, Sierksma.FB.BadY S → Sierksma.FB.BadY (S.image (Sierksma.FB.relIdx p)) ∧
      (S.image (Sierksma.FB.relIdx p)).card = S.card ∧
      Sierksma.FB.mult (S.image (Sierksma.FB.relIdx p)) 36 = Sierksma.FB.mult S 36 ∧
      (∀ f < 36, ∃ g < 36, Sierksma.FB.mult (S.image (Sierksma.FB.relIdx p)) f = Sierksma.FB.mult S g)) := by
  classical
  obtain ⟨π, hπ⟩ := validPerm_equiv p hp
  have hr := relIdx_spec π p hπ
  have he := pe_transport p hp
  have heinj : Set.InjOn (epOf p) (↑(Finset.range 36) : Set ℕ) := by
    intro f hf g hg hfg
    exact he.2.1 f (Finset.mem_range.mp hf) g (Finset.mem_range.mp hg) hfg
  have heimg : (Finset.range 36).image (epOf p) = Finset.range 36 := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_range.mpr (he.1 f (Finset.mem_range.mp hf))
    · rw [Finset.card_image_iff.mpr heinj]
  have hesur (g : ℕ) (hg : g < 36) : ∃ f < 36, epOf p f = g := by
    have hmem : g ∈ (Finset.range 36).image (epOf p) := by rw [heimg]; exact Finset.mem_range.mpr hg
    obtain ⟨f,hf,heq⟩ := Finset.mem_image.mp hmem
    exact ⟨f,Finset.mem_range.mp hf,heq⟩
  have hzero (f : ℕ) : tau1 f = 0 → f = 35 := by
    intro hz
    by_contra hn
    have hb : Nat.beq f 35 = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact hn (Nat.eq_of_beq_eq_true h)
    cases hc : Nat.ble 7 (ev f) <;> simp [tau1,hb,hc] at hz
  have he35 : epOf p 35 = 35 := hzero _ (by rw [ht 35 (by omega)]; rfl)
  have hsep (j : ℕ) (hj : j < 1855) :
      Nat.testBit (intt 36) (relIdx p j) = Nat.testBit (intt 36) j := by
    rw [tab_pe.2.2.1 _ (hr.1 j hj).1,tab_pe.2.2.1 j hj]
    simpa only [he35] using congrArg Bool.not (he.2.2.2 j hj 35 (by omega))
  have hlabsum (τ : ℕ → ℕ) (j : ℕ) : lab τ j =
      ∑ f ∈ Finset.range 36, cond (Nat.testBit (intt f) j) (64 ^ τ f) 0 := by
    unfold lab
    have hn (n : ℕ) : Nat.rec (motive := fun _ => ℕ) 0
        (fun f acc => Nat.add acc (cond (Nat.testBit (intt f) j) (Nat.pow 64 (τ f)) 0)) n =
        ∑ f ∈ Finset.range n, cond (Nat.testBit (intt f) j) (64 ^ τ f) 0 := by
      induction n with
      | zero => simp
      | succ n hn => simp only [Nat.rec,hn,Finset.sum_range_succ]; rfl
    exact hn 36
  have hlab (τ : ℕ → ℕ) (hτ : ∀ f < 36, τ (epOf p f) = τ f) (j : ℕ) (hj : j < 1855) :
      lab τ (relIdx p j) = lab τ j := by
    calc
      lab τ (relIdx p j) = ∑ f ∈ Finset.range 36,
          cond (Nat.testBit (intt f) (relIdx p j)) (64 ^ τ f) 0 := hlabsum τ _
      _ = ∑ f ∈ (Finset.range 36).image (epOf p),
          cond (Nat.testBit (intt f) (relIdx p j)) (64 ^ τ f) 0 := by rw [heimg]
      _ = ∑ f ∈ Finset.range 36,
          cond (Nat.testBit (intt (epOf p f)) (relIdx p j)) (64 ^ τ (epOf p f)) 0 :=
        Finset.sum_image (f := fun f => cond (Nat.testBit (intt f) (relIdx p j)) (64 ^ τ f) 0) heinj
      _ = ∑ f ∈ Finset.range 36, cond (Nat.testBit (intt f) j) (64 ^ τ f) 0 := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [he.2.2.2 j hj f (Finset.mem_range.mp hf),hτ f (Finset.mem_range.mp hf)]
      _ = lab τ j := (hlabsum τ j).symm
  have hL1 (j : ℕ) (hj : j < 1855) : L1t (relIdx p j) = L1t j := by
    rw [(labtab _ (hr.1 j hj).1).1,(labtab j hj).1]
    exact hlab tau1 ht j hj
  have hL2 (k : ℕ) (hk : k < 6) (r : ℕ) (hrr : r < 1855)
      (hkroot : R1.getD k 0 = r) (hfix : relIdx p r = r) (j : ℕ) (hj : j < 1855) :
      L2t k (relIdx p j) = L2t k j := by
    rw [(labtab _ (hr.1 j hj).1).2 k hk,(labtab j hj).2 k hk]
    refine hlab (tau2 (R1.getD k 0)) ?_ j hj
    intro f hf
    unfold tau2
    rw [ht f hf,hkroot]
    have hh := he.2.2.2 r hrr f hf
    rw [hfix] at hh
    rw [hh]
  refine ⟨fun j hj => ⟨hL1 j hj,hsep j hj⟩,hL2,?_⟩
  intro S hS
  obtain ⟨y,hsupp,hy,hyS⟩ := hS
  have hbound (j : ℕ) (hj : j ∈ S) : j < 1855 := by
    rw [← hyS] at hj
    exact (index_transfer y hsupp hy).2.1 j hj
  have hinj : Set.InjOn (relIdx p) (↑S : Set ℕ) := by
    intro i hi j hj hij
    exact hr.2 i (hbound i hi) j (hbound j hj) hij
  obtain ⟨y',hy',hsupp',heq⟩ := relabel_idx y hsupp hy p hp
  have hbad : BadY (S.image (relIdx p)) := by
    refine ⟨y',hsupp',hy',?_⟩
    simpa only [hyS] using heq
  have hm (f : ℕ) (g : ℕ) (hh : ∀ j ∈ S,
      Nat.testBit (intt g) (relIdx p j) = Nat.testBit (intt f) j) :
      mult (S.image (relIdx p)) g = mult S f := by
    unfold mult
    have hset : ((S.image (relIdx p)).filter (fun j => Nat.testBit (intt g) j = true)) =
        (S.filter (fun j => Nat.testBit (intt f) j = true)).image (relIdx p) := by
      ext x
      constructor
      · intro hx
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).1
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,by
          simpa only [hh j hj] using (Finset.mem_filter.mp hx).2⟩,rfl⟩
      · rintro hx
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
        have hjS := (Finset.mem_filter.mp hj).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,hjS,rfl⟩,by
          simpa only [hh j hjS] using (Finset.mem_filter.mp hj).2⟩
    rw [hset]
    exact Finset.card_image_iff.mpr (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))
  refine ⟨hbad,Finset.card_image_iff.mpr hinj,hm 36 36 (fun j hj => hsep j (hbound j hj)),?_⟩
  intro f hf
  obtain ⟨g,hg,hgf⟩ := hesur f hf
  refine ⟨g,hg,?_⟩
  rw [← hgf]
  exact hm g (epOf p g) (fun j hj => he.2.2.2 j (hbound j hj) g hg)
