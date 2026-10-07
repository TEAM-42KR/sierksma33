import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_cov
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_col
import SierksmaLean.Theorems.Thm_Sierksma_respects_two_orientations
open Common Sierksma Sierksma.FB
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem proof_Sierksma_FB_covOf_spec :
    (∀ g < 76545, Sierksma.ValidConstraint 3 (Sierksma.FB.constraintOf g)) ∧
    (∀ q : Sierksma.PairConstraint 9, Sierksma.ValidConstraint 3 q → ∃ g < 76545, Sierksma.FB.constraintOf g = q) ∧
    (∀ g < 76545, ∀ i < 1855,
      Nat.testBit (Sierksma.FB.covOf g) i = true ↔ Sierksma.Covers (Sierksma.FB.partOf i) (Sierksma.FB.constraintOf g)) := by
  classical
  obtain ⟨hnt, he, hei, hspl, hrank⟩ := Sierksma.FB.tab_cov
  have hedge (f : ℕ) (hf : f < 36) :
      (edgeOf f).1.val = eu f ∧ (edgeOf f).2.val = ev f := by
    have h := he f hf
    change eu f % 9 = eu f ∧ ev f % 9 = ev f
    exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h.2⟩
  have hinj (f f' : ℕ) (hf : f < 36) (hf' : f' < 36) (h : edgeOf f = edgeOf f') : f = f' := by
    have hfu := (congrArg (fun e : Edge 9 => e.1.val) h)
    have hfv := (congrArg (fun e : Edge 9 => e.2.val) h)
    rw [(hedge f hf).1, (hedge f' hf').1] at hfu
    rw [(hedge f hf).2, (hedge f' hf').2] at hfv
    have hfi := hei (eu f) (by have hh := he f hf; omega) (ev f) (he f hf).2 (he f hf).1
    have hfj := hei (eu f') (by have hh := he f' hf'; omega) (ev f') (he f' hf').2 (he f' hf').1
    have hleft : ∀ f < 36, eIdx (eu f) (ev f) = f := by
      intro a ha
      interval_cases a <;> decide
    rw [← hleft f hf, ← hleft f' hf', hfu, hfv]
  have hdisj (f f' : ℕ) (hf : f < 36) (hf' : f' < 36) (hd : edisj f f' = true) :
      Disjoint (Endpoints (edgeOf f)) (Endpoints (edgeOf f')) := by
    have hfd := hedge f hf
    have hgd := hedge f' hf'
    simp only [edisj, Bool.and_eq_true, Bool.not_eq_true'] at hd
    simp only [Endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · constructor
      · intro hh
        have hval := congrArg Fin.val hh
        rw [hfd.1, hgd.1] at hval
        exact Nat.ne_of_beq_eq_false hd.1.1.1 hval
      · intro hh
        have hval := congrArg Fin.val hh
        rw [hfd.1, hgd.2] at hval
        exact Nat.ne_of_beq_eq_false hd.1.1.2 hval
    · constructor
      · intro hh
        have hval := congrArg Fin.val hh
        rw [hfd.2, hgd.1] at hval
        exact Nat.ne_of_beq_eq_false hd.1.2 hval
      · intro hh
        have hval := congrArg Fin.val hh
        rw [hfd.2, hgd.2] at hval
        exact Nat.ne_of_beq_eq_false hd.2 hval
  have hs (m : ℕ) (hm : m < 945) :
      (∀ k : Fin 4, splE m k.val < 36) ∧
      (∀ j k : Fin 4, j < k → splE m j.val < splE m k.val) ∧
      (∀ j k : Fin 4, j < k → edisj (splE m j.val) (splE m k.val) = true) := by
    obtain ⟨h01,h12,h23,h3,d01,d02,d03,d12,d13,d23⟩ := hspl m hm
    refine ⟨?_, ?_, ?_⟩
    · intro k; fin_cases k <;> dsimp <;> omega
    · intro j k hjk; fin_cases j <;> fin_cases k <;> dsimp at * <;> omega
    · intro j k hjk; fin_cases j <;> fin_cases k <;> dsimp at * <;> first | omega | assumption
  have hv : ∀ g < 76545, ValidConstraint 3 (constraintOf g) := by
    intro g hg
    let m := g / 81
    have hm : m < 945 := by dsimp [m]; omega
    have hs' := hs m hm
    let E : Fin 4 → Edge 9 := fun k => edgeOf (splE m k.val)
    have hEinj : Function.Injective E := by
      intro j k hjk
      have hf := hinj _ _ (hs'.1 j) (hs'.1 k) hjk
      by_contra hjk'
      rcases lt_or_gt_of_ne hjk' with h | h
      · have hh := hs'.2.1 j k h; omega
      · have hh := hs'.2.1 k j h; omega
    have hmch : (constraintOf g).matching = Finset.univ.image E := by
      ext e
      simp only [constraintOf, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and, m, E]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩
      · rintro ⟨k,rfl⟩; fin_cases k <;> simp
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro e he'
      rw [hmch] at he'
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he'
      have h := he _ (hs'.1 k)
      change (edgeOf _).1.val < (edgeOf _).2.val
      rw [(hedge _ (hs'.1 k)).1, (hedge _ (hs'.1 k)).2]
      exact h.1
    · intro e he' f hf' hef
      rw [hmch] at he' hf'
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hf'
      have hjk : j ≠ k := fun h => hef (congrArg E h)
      rcases lt_or_gt_of_ne hjk with hjk | hkj
      · exact hdisj _ _ (hs'.1 j) (hs'.1 k) (hs'.2.2 j k hjk)
      · exact (hdisj _ _ (hs'.1 k) (hs'.1 j) (hs'.2.2 k j hkj)).symm
    · rw [hmch, Finset.card_image_of_injective _ hEinj]
      decide
    · intro e he'
      simp only [constraintOf, Finset.mem_insert, Finset.mem_singleton, not_or] at he'
      simp only [constraintOf, if_neg he'.1, if_neg he'.2.1, if_neg he'.2.2.1, if_neg he'.2.2.2]
  refine ⟨hv, ?_, ?_⟩
  · intro q hq
    let idx : Edge 9 → ℕ := fun e => eIdx e.1.val e.2.val
    have hidx (e : Edge 9) (he' : e ∈ q.matching) : idx e < 36 ∧ edgeOf (idx e) = e := by
      have h := hei e.1.val e.1.isLt e.2.val e.2.isLt (hq.1.1 e he')
      refine ⟨h.2.2, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact (hedge _ h.2.2).1.trans h.1
      · exact (hedge _ h.2.2).2.trans h.2.1
    have hidxinj : Set.InjOn idx q.matching := by
      intro e he' f hf' h
      rw [← (hidx e he').2, ← (hidx f hf').2, h]
    let L := q.matching.image idx
    have hL : L.card = 4 := (Finset.card_image_of_injOn hidxinj).trans hq.2.1
    let e : Fin 4 → ℕ := L.orderEmbOfFin hL
    have hem (k : Fin 4) : e k ∈ L := L.orderEmbOfFin_mem hL k
    have heq (k : Fin 4) : e k < 36 ∧ edgeOf (e k) ∈ q.matching := by
      obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp (hem k)
      rw [← hea]
      exact ⟨(hidx a ha).1, by rw [(hidx a ha).2]; exact ha⟩
    have hmono : StrictMono e := (L.orderEmbOfFin hL).strictMono
    have henum (a : Edge 9) : a ∈ q.matching ↔ ∃ k : Fin 4, edgeOf (e k) = a := by
      constructor
      · intro ha
        have him : idx a ∈ L := Finset.mem_image.mpr ⟨a, ha, rfl⟩
        obtain ⟨k, hk⟩ := (L.orderIsoOfFin hL).surjective ⟨idx a, him⟩
        have hk' : e k = idx a := congrArg Subtype.val hk
        exact ⟨k, (congrArg edgeOf hk').trans (hidx a ha).2⟩
      · rintro ⟨k, rfl⟩
        exact (heq k).2
    have hed (j k : Fin 4) (hjk : j < k) : edisj (e j) (e k) = true := by
      have hne : edgeOf (e j) ≠ edgeOf (e k) := by
        intro hh
        have hh' := hinj _ _ (heq j).1 (heq k).1 hh
        have hlt := hmono hjk
        omega
      have hd := hq.1.2 _ (heq j).2 _ (heq k).2 hne
      have hej := he _ (heq j).1
      have hek := he _ (heq k).1
      simp only [edisj, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
      simp only [Endpoints, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
        Finset.mem_insert, Finset.mem_singleton, not_or, and_assoc] at hd
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply Bool.eq_false_iff.mpr
        intro hh; apply hd.1; apply Fin.ext
        rw [(hedge _ (heq j).1).1, (hedge _ (heq k).1).1]; exact Nat.eq_of_beq_eq_true hh
      · apply Bool.eq_false_iff.mpr
        intro hh; apply hd.2.1; apply Fin.ext
        rw [(hedge _ (heq j).1).1, (hedge _ (heq k).1).2]; exact Nat.eq_of_beq_eq_true hh
      · apply Bool.eq_false_iff.mpr
        intro hh; apply hd.2.2.1; apply Fin.ext
        rw [(hedge _ (heq j).1).2, (hedge _ (heq k).1).1]; exact Nat.eq_of_beq_eq_true hh
      · apply Bool.eq_false_iff.mpr
        intro hh; apply hd.2.2.2; apply Fin.ext
        rw [(hedge _ (heq j).1).2, (hedge _ (heq k).1).2]; exact Nat.eq_of_beq_eq_true hh
    obtain ⟨hm,h0,h1,h2,h3⟩ := hrank (e 0) (heq 0).1 (e 1) (heq 1).1 (e 2) (heq 2).1 (e 3) (heq 3).1
      (hmono (by decide : (0 : Fin 4) < 1)) (hmono (by decide : (1 : Fin 4) < 2))
      (hmono (by decide : (2 : Fin 4) < 3)) (hed 0 1 (by decide)) (hed 0 2 (by decide))
      (hed 0 3 (by decide)) (hed 1 2 (by decide)) (hed 1 3 (by decide)) (hed 2 3 (by decide))
    let m := mRank (e 0) (e 1) (e 2) (e 3)
    have hrec (k : Fin 4) : splE m k.val = e k := by
      fin_cases k <;> first | exact h0 | exact h1 | exact h2 | exact h3
    have hrec0 : splE m 0 = e 0 := hrec 0
    have hrec1 : splE m 1 = e 1 := hrec 1
    have hrec2 : splE m 2 = e 2 := hrec 2
    have hrec3 : splE m 3 = e 3 := hrec 3
    let t : Fin 4 → ℕ := fun k => (q.twists (edgeOf (e k))).val
    have ht (k : Fin 4) : t k < 3 := ZMod.val_lt _
    let c := t 0 + 3 * t 1 + 9 * t 2 + 27 * t 3
    have hc : c < 81 := by have := ht 0; have := ht 1; have := ht 2; have := ht 3; dsimp [c]; omega
    have hdigits : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ d < 3,
        twistDigit (a + 3*b + 9*c + 27*d) 0 = a ∧
        twistDigit (a + 3*b + 9*c + 27*d) 1 = b ∧
        twistDigit (a + 3*b + 9*c + 27*d) 2 = c ∧
        twistDigit (a + 3*b + 9*c + 27*d) 3 = d := by
      intro a ha b hb c hc d hd
      interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> decide
    obtain ⟨ht0,ht1,ht2,ht3⟩ := hdigits (t 0) (ht 0) (t 1) (ht 1) (t 2) (ht 2) (t 3) (ht 3)
    let g := 81*m + c
    have hgm : g / 81 = m := by dsimp [g]; omega
    have hgc : g % 81 = c := by dsimp [g]; omega
    have hmatching : (constraintOf g).matching = q.matching := by
      ext a
      simp only [constraintOf, hgm, hrec0,hrec1,hrec2,hrec3, Finset.mem_insert, Finset.mem_singleton]
      rw [henum]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩
      · rintro ⟨k,rfl⟩; fin_cases k <;> simp
    refine ⟨g, by dsimp [g]; omega, ?_⟩
    have hex : ∀ q r : PairConstraint 9, q.matching = r.matching → q.twists = r.twists → q = r := by
      intro q r hm ht
      cases q; cases r; cases hm; cases ht; rfl
    apply hex _ _ hmatching
    funext a
    by_cases ha : a ∈ q.matching
    · obtain ⟨k, rfl⟩ := (henum a).mp ha
      have hneq (j k : Fin 4) (hjk : j ≠ k) : edgeOf (e j) ≠ edgeOf (e k) := by
        intro hh
        exact hjk ((L.orderEmbOfFin hL).injective (hinj _ _ (heq j).1 (heq k).1 hh))
      fin_cases k <;>
        simp [constraintOf, hgm,hgc,hrec0,hrec1,hrec2,hrec3, c, ht0,ht1,ht2,ht3, t,
          if_pos rfl, if_neg (hneq 1 0 (by decide)), if_neg (hneq 2 0 (by decide)),
          if_neg (hneq 2 1 (by decide)), if_neg (hneq 3 0 (by decide)),
          if_neg (hneq 3 1 (by decide)), if_neg (hneq 3 2 (by decide)), ZMod.natCast_zmod_val]
    · have hb : a ∉ (constraintOf g).matching := by rwa [hmatching]
      rw [(hv g (by dsimp [g]; omega)).2.2 a hb, hq.2.2 a ha]
  · intro g hg i hi
    let m := g / 81
    let c := g % 81
    have hm : m < 945 := by dsimp [m]; omega
    have hsp := hs m hm
    let E : Fin 4 → ℕ := fun k => splE m k.val
    let D : Fin 4 → ℕ := fun k => dI i (eu (E k)) (ev (E k))
    let T : Fin 4 → ℕ := fun k => twistDigit c k.val
    have hT (k : Fin 4) : T k < 3 := Nat.mod_lt _ (by decide)
    have hD (k : Fin 4) : D k < 3 := Nat.mod_lt _ (by decide)
    have hcast : ∀ (a : ℕ), a < 3 → ∀ (b : ℕ), b < 3 → (((a : ℕ) : ZMod 3) = (b : ZMod 3) ↔ a = b) := by
      intro a ha b hb
      interval_cases a <;> interval_cases b <;> decide
    have hsub : ∀ (a : ℕ), a < 3 → ∀ (b : ℕ), b < 3 →
        (((b + 3 - a) % 3 : ℕ) : ZMod 3) = (b : ZMod 3) - (a : ZMod 3) := by
      intro a ha b hb
      interval_cases a <;> interval_cases b <;> decide
    have hneg : ∀ a < 3, ((neg3 a : ℕ) : ZMod 3) = -(a : ZMod 3) := by
      intro a ha; interval_cases a <;> decide
    have hneglt (a : ℕ) : neg3 a < 3 := Nat.mod_lt _ (by decide)
    have hcols (v : Fin 9) : colOf i v.val < 3 := (Sierksma.FB.tab_col.1 i hi).2.1 v.val v.isLt
    let col : Fin 9 → ZMod 3 := fun v => (colOf i v.val : ZMod 3)
    have hres : Respects (partOf i) col := by
      intro u v
      change (colOf i u.val : ZMod 3) = (colOf i v.val : ZMod 3) ↔ _
      rw [hcast _ (hcols u) _ (hcols v)]
      constructor
      · intro huv
        let a : Fin 3 := ⟨colOf i u.val, hcols u⟩
        refine ⟨Finset.univ.filter (fun v : Fin 9 => colOf i v.val = a.val), ?_, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
        · simp [a]
        · simp [a, huv]
      · rintro ⟨A,hA,hu,hv'⟩
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
        exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv').2.symm
    have hresneg : Respects (partOf i) (fun v => -col v) := by
      intro u v
      rw [neg_inj]
      exact hres u v
    have hdiff (k : Fin 4) :
        col (edgeOf (E k)).2 - col (edgeOf (E k)).1 = (D k : ZMod 3) := by
      have hf := hsp.1 k
      have hh := (hsub _ (hcols (edgeOf (E k)).1) _ (hcols (edgeOf (E k)).2)).symm
      dsimp only [col,D,dI]
      rw [(hedge _ hf).1, (hedge _ hf).2] at hh ⊢
      exact hh
    have henum (a : Edge 9) : a ∈ (constraintOf g).matching ↔ ∃ k : Fin 4, edgeOf (E k) = a := by
      simp only [constraintOf, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl | rfl) <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩
      · rintro ⟨k,rfl⟩; fin_cases k <;> simp [E,m]
    have htw (k : Fin 4) : (constraintOf g).twists (edgeOf (E k)) = (T k : ZMod 3) := by
      have hneq (j k : Fin 4) (hjk : j ≠ k) : edgeOf (E j) ≠ edgeOf (E k) := by
        intro hh
        have hh' := hinj _ _ (hsp.1 j) (hsp.1 k) hh
        rcases lt_or_gt_of_ne hjk with hjk | hkj
        · have hlt := hsp.2.1 j k hjk; exact hlt.ne hh'
        · have hlt := hsp.2.1 k j hkj; exact hlt.ne hh'.symm
      have hn10 : edgeOf (splE (g / 81) 1) ≠ edgeOf (splE (g / 81) 0) := hneq 1 0 (by decide)
      have hn20 : edgeOf (splE (g / 81) 2) ≠ edgeOf (splE (g / 81) 0) := hneq 2 0 (by decide)
      have hn21 : edgeOf (splE (g / 81) 2) ≠ edgeOf (splE (g / 81) 1) := hneq 2 1 (by decide)
      have hn30 : edgeOf (splE (g / 81) 3) ≠ edgeOf (splE (g / 81) 0) := hneq 3 0 (by decide)
      have hn31 : edgeOf (splE (g / 81) 3) ≠ edgeOf (splE (g / 81) 1) := hneq 3 1 (by decide)
      have hn32 : edgeOf (splE (g / 81) 3) ≠ edgeOf (splE (g / 81) 2) := hneq 3 2 (by decide)
      fin_cases k <;> simp [constraintOf,E,T,m,c,hn10,hn20,hn21,hn30,hn31,hn32]
    have hcov : Covers (partOf i) (constraintOf g) ↔
        (∀ k : Fin 4, (D k : ZMod 3) ≠ (T k : ZMod 3)) ∨
        (∀ k : Fin 4, -(D k : ZMod 3) ≠ (T k : ZMod 3)) := by
      constructor
      · rintro ⟨col',hr',hn'⟩
        have hor : (∀ x y, col' y - col' x = col y - col x) ∨
            (∀ x y, col' y - col' x = -(col y - col x)) := by
          by_cases hh : ∀ x y, col x = col y
          · left
            intro x y
            have heq := (hr' x y).mpr ((hres x y).mp (hh x y))
            rw [← heq, ← hh x y, sub_self, sub_self]
          · push_neg at hh
            obtain ⟨x,y,hxy⟩ := hh
            exact Sierksma.respects_two_orientations (partOf i) col col' hres hr' x y hxy
        rcases hor with hp | hn
        · left; intro k
          have hn' := hn' (edgeOf (E k)) ((henum _).mpr ⟨k,rfl⟩)
          rwa [hp, hdiff k, htw k] at hn'
        · right; intro k
          have hn' := hn' (edgeOf (E k)) ((henum _).mpr ⟨k,rfl⟩)
          rwa [hn, hdiff k, htw k] at hn'
      · rintro (hp | hn)
        · refine ⟨col,hres,?_⟩
          intro a ha
          obtain ⟨k,rfl⟩ := (henum a).mp ha
          rw [hdiff k,htw k]
          exact hp k
        · refine ⟨(fun v => -col v),hresneg,?_⟩
          intro a ha
          obtain ⟨k,rfl⟩ := (henum a).mp ha
          change -col (edgeOf (E k)).2 - -col (edgeOf (E k)).1 ≠ _
          have hnn : -col (edgeOf (E k)).2 - -col (edgeOf (E k)).1 =
              -(col (edgeOf (E k)).2 - col (edgeOf (E k)).1) := by ring
          rw [hnn, hdiff k, htw k]
          exact hn k
    have hbits : Nat.testBit (covOf g) i = true ↔
        (∀ k : Fin 4, D k ≠ T k) ∨ (∀ k : Fin 4, D k ≠ neg3 (T k)) := by
      have hnt' (k : Fin 4) : (nt (3 * E k + T k)).testBit i = !Nat.beq (D k) (T k) :=
        hnt i hi (E k) (hsp.1 k) (T k) (hT k)
      have hntn (k : Fin 4) : (nt (3 * E k + neg3 (T k))).testBit i = !Nat.beq (D k) (neg3 (T k)) :=
        hnt i hi (E k) (hsp.1 k) (neg3 (T k)) (hneglt _)
      have hbeq (a b : ℕ) : (!(Nat.beq a b)) = true ↔ a ≠ b := by
        constructor
        · intro h
          rw [Bool.not_eq_true'] at h
          exact Nat.ne_of_beq_eq_false h
        · intro h; rw [Bool.not_eq_true']; apply Bool.eq_false_iff.mpr
          intro hh; exact h (Nat.eq_of_beq_eq_true hh)
      have hforall (P : Fin 4 → Prop) : (P 0 ∧ P 1 ∧ P 2 ∧ P 3) ↔ ∀ k, P k := by
        constructor
        · rintro ⟨h0,h1,h2,h3⟩ k; fin_cases k <;> assumption
        · intro h; exact ⟨h 0,h 1,h 2,h 3⟩
      have hland (a b n : ℕ) : Nat.testBit (Nat.land a b) n = (Nat.testBit a n && Nat.testBit b n) :=
        Nat.testBit_land a b n
      have hlor (a b n : ℕ) : Nat.testBit (Nat.lor a b) n = (Nat.testBit a n || Nat.testBit b n) :=
        Nat.testBit_lor a b n
      simp only [covOf,hlor,hland,Bool.or_eq_true,Bool.and_eq_true]
      change (((nt (3 * E 0 + T 0)).testBit i = true ∧ (nt (3 * E 1 + T 1)).testBit i = true) ∧
          ((nt (3 * E 2 + T 2)).testBit i = true ∧ (nt (3 * E 3 + T 3)).testBit i = true)) ∨
        (((nt (3 * E 0 + neg3 (T 0))).testBit i = true ∧ (nt (3 * E 1 + neg3 (T 1))).testBit i = true) ∧
          ((nt (3 * E 2 + neg3 (T 2))).testBit i = true ∧ (nt (3 * E 3 + neg3 (T 3))).testBit i = true)) ↔ _
      rw [hnt' 0,hnt' 1,hnt' 2,hnt' 3,hntn 0,hntn 1,hntn 2,hntn 3]
      simp only [hbeq,and_assoc]
      exact or_congr (hforall (fun k => D k ≠ T k)) (hforall (fun k => D k ≠ neg3 (T k)))
    rw [hbits,hcov]
    have hp : (∀ k : Fin 4, D k ≠ T k) ↔ ∀ k : Fin 4, (D k : ZMod 3) ≠ (T k : ZMod 3) := by
      apply forall_congr'; intro k
      exact (not_congr (hcast _ (hD k) _ (hT k))).symm
    have hn : (∀ k : Fin 4, D k ≠ neg3 (T k)) ↔ ∀ k : Fin 4, -(D k : ZMod 3) ≠ (T k : ZMod 3) := by
      apply forall_congr'; intro k
      simp only [ne_eq]
      rw [← hcast _ (hD k) _ (hneglt (T k)),hneg _ (hT k)]
      exact ⟨fun h heq => h (by rw [← heq,neg_neg]), fun h heq => h (by rw [heq,neg_neg])⟩
    exact or_congr hp hn
