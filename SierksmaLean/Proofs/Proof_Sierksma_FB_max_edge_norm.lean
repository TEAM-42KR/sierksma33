import SierksmaLean.Theorems.Thm_Sierksma_FB_index_transfer
import SierksmaLean.Theorems.Thm_Sierksma_FB_relabel_idx
import SierksmaLean.Theorems.Thm_Sierksma_FB_relIdx_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_pe_transport
import SierksmaLean.Theorems.Thm_Sierksma_FB_enormtab
set_option autoImplicit false
open Common Sierksma Sierksma.FB
set_option maxRecDepth 10000
set_option maxHeartbeats 600000

theorem proof_Sierksma_FB_max_edge_norm (S : Finset ℕ) (hS : Sierksma.FB.BadY S) :
    ∃ S0 : Finset ℕ, Sierksma.FB.BadY S0 ∧ S0.card = S.card ∧
      ∀ f < 36, Sierksma.FB.mult S0 f ≤ Sierksma.FB.mult S0 35 := by
  classical
  obtain ⟨y, hsupp, hy, hidx⟩ := hS
  have hbound : ∀ i ∈ S, i < 1855 := by
    rw [← hidx]
    exact (index_transfer y hsupp hy).2.1
  obtain ⟨fm, hfm, hmax⟩ := Finset.exists_max_image (Finset.range 36) (mult S)
    (by exact ⟨0, by simp⟩)
  have hfm36 : fm < 36 := Finset.mem_range.mp hfm
  let p := enorm fm
  have hp : validPerm p = true := (enormtab fm hfm36).1
  have hep : epOf p fm = 35 := (enormtab fm hfm36).2
  have hpe := pe_transport p hp
  have hp0 : (List.range 9).all (fun v => Nat.blt (pAt p v) 9) = true :=
    (Bool.and_eq_true_iff.mp hp).1
  have hp1 : (List.range 9).all (fun v => (List.range 9).all
      (fun w => Nat.beq v w || !(Nat.beq (pAt p v) (pAt p w)))) = true :=
    (Bool.and_eq_true_iff.mp hp).2
  have hlt (v : Fin 9) : pAt p v.val < 9 := by
    have hh := (List.all_eq_true.mp hp0) v.val (List.mem_range.mpr v.isLt)
    simpa using hh
  let ff : Fin 9 → Fin 9 := fun v => ⟨pAt p v.val, hlt v⟩
  have hff : Function.Injective ff := by
    intro v w h
    have hh := (List.all_eq_true.mp
      ((List.all_eq_true.mp hp1) v.val (List.mem_range.mpr v.isLt))) w.val
      (List.mem_range.mpr w.isLt)
    have he : pAt p v.val = pAt p w.val := congrArg Fin.val h
    have hv : v.val = w.val := by simpa [he] using hh
    exact Fin.ext hv
  let π : Equiv.Perm (Fin 9) := Equiv.ofBijective ff ((Finite.injective_iff_bijective).mp hff)
  have hπ (v : Fin 9) : (π v).val = pAt p v.val := rfl
  have hrs := relIdx_spec π p hπ
  have hri : Set.InjOn (relIdx p) (S : Set ℕ) := by
    intro i hi j hj hij
    exact hrs.2 i (hbound i hi) j (hbound j hj) hij
  let S0 := S.image (relIdx p)
  have hcard : S0.card = S.card := Finset.card_image_of_injOn hri
  have hBad0 : BadY S0 := by
    obtain ⟨y', hy', hsupp', hi'⟩ := relabel_idx y hsupp hy p hp
    refine ⟨y', hsupp', hy', ?_⟩
    simpa only [hidx] using hi'
  have hmult (g : ℕ) (hg : g < 36) : mult S0 (epOf p g) = mult S g := by
    unfold mult
    change ((S.image (relIdx p)).filter (fun i => Nat.testBit (intt (epOf p g)) i = true)).card = _
    rw [Finset.filter_image]
    have hfilter : S.filter (fun i => Nat.testBit (intt (epOf p g)) (relIdx p i) = true) =
        S.filter (fun i => Nat.testBit (intt g) i = true) := by
      apply Finset.filter_congr
      intro i hi
      rw [hpe.2.2.2 i (hbound i hi) g hg]
    rw [hfilter]
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    exact hri (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
  have hm35 : mult S0 35 = mult S fm := by simpa only [hep] using hmult fm hfm36
  let ef : Fin 36 → Fin 36 := fun f => ⟨epOf p f.val, hpe.1 f.val f.isLt⟩
  have hefinj : Function.Injective ef := by
    intro f g h
    apply Fin.ext
    exact hpe.2.1 f.val f.isLt g.val g.isLt (congrArg Fin.val h)
  have hefsurj : Function.Surjective ef := ((Finite.injective_iff_bijective).mp hefinj).2
  refine ⟨S0, hBad0, hcard, ?_⟩
  intro f hf
  obtain ⟨g, hgf⟩ := hefsurj ⟨f, hf⟩
  have hgf' : epOf p g.val = f := congrArg Fin.val hgf
  have hmg : mult S0 f = mult S g.val := by simpa only [hgf'] using hmult g.val g.isLt
  rw [hmg, hm35]
  exact hmax g.val (Finset.mem_range.mpr g.isLt)
