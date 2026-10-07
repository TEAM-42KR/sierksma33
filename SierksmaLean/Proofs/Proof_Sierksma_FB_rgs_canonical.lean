import SierksmaLean.Definitions.Def_Sierksma_FBChecker
import SierksmaLean.Theorems.Thm_Sierksma_FB_fibre_partition_spec
set_option autoImplicit false
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1000000

theorem proof_Sierksma_FB_rgs_canonical (c : Fin 9 → Fin 3) (hs : Function.Surjective c)
    (hr : ∀ v : Fin 9, 0 < (c v).val → ∃ w : Fin 9, w < v ∧ (c w).val + 1 = (c v).val) :
    ∀ v : Fin 9, Sierksma.CanonColour
      ((Finset.univ : Finset (Fin 3)).image (fun a => Finset.univ.filter (fun w : Fin 9 => c w = a))) v =
      ((c v).val : ZMod 3) := by
  classical
  let B := fun a : Fin 3 => Finset.univ.filter (fun v : Fin 9 => c v = a)
  let Q : Common.Partition 9 := Finset.univ.image B
  have mem (v : Fin 9) (a : Fin 3) : v ∈ B a ↔ c v = a := by simp [B]
  have ne (a : Fin 3) : (B a).Nonempty := by
    obtain ⟨v,hv⟩ := hs a
    exact ⟨v,(mem v a).mpr hv⟩
  let m (a : Fin 3) : Fin 9 := (B a).min' (ne a)
  have mc (a : Fin 3) : c (m a) = a := (mem (m a) a).mp (Finset.min'_mem _ _)
  have ml (a : Fin 3) (v : Fin 9) (hv : c v = a) : m a ≤ v :=
    Finset.min'_le _ v ((mem v a).mpr hv)
  have mi : Function.Injective m := by
    intro a b h
    exact (mc a).symm.trans ((congrArg c h).trans (mc b))
  have h01 : m 0 < m 1 := by
    obtain ⟨w,hw,hc⟩ := hr (m 1) (by rw [mc]; decide)
    have hw0 : c w = 0 := by apply Fin.ext; rw [mc] at hc; change (c w).val + 1 = 1 at hc; omega
    exact lt_of_le_of_lt (ml 0 w hw0) hw
  have h12 : m 1 < m 2 := by
    obtain ⟨w,hw,hc⟩ := hr (m 2) (by rw [mc]; decide)
    have hw1 : c w = 1 := by apply Fin.ext; rw [mc] at hc; change (c w).val + 1 = 2 at hc; omega
    exact lt_of_le_of_lt (ml 1 w hw1) hw
  have h02 : m 0 < m 2 := lt_trans h01 h12
  have ord (a b : Fin 3) : m a < m b ↔ a < b := by
    fin_cases a <;> fin_cases b
    · change m 0 < m 0 ↔ (0 : Fin 3) < 0
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 0 < m 1 ↔ (0 : Fin 3) < 1
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 0 < m 2 ↔ (0 : Fin 3) < 2
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 1 < m 0 ↔ (1 : Fin 3) < 0
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 1 < m 1 ↔ (1 : Fin 3) < 1
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 1 < m 2 ↔ (1 : Fin 3) < 2
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 2 < m 0 ↔ (2 : Fin 3) < 0
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 2 < m 1 ↔ (2 : Fin 3) < 1
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
    · change m 2 < m 2 ↔ (2 : Fin 3) < 2
      simp only [Fin.lt_def] at h01 h12 h02 ⊢
      omega
  have rel (u v : Fin 9) : (∃ A ∈ Q, u ∈ A ∧ v ∈ A) ↔ c u = c v :=
    (fibre_partition_spec c hs).2 u v
  have minimum (u : Fin 9) :
      (∀ w : Fin 9, w < u → ¬ ∃ A ∈ Q, w ∈ A ∧ u ∈ A) ↔ m (c u) = u := by
    constructor
    · intro hu
      apply le_antisymm (ml (c u) u rfl)
      apply le_of_not_gt
      intro hlt
      exact hu (m (c u)) hlt ((rel _ _).mpr (mc _))
    · intro hu w hw hrel
      have hc := (rel w u).mp hrel
      have hl := ml (c u) w hc
      rw [hu] at hl
      exact (not_lt_of_ge hl) hw
  have below (u v : Fin 9) :
      (∀ w : Fin 9, (∃ A ∈ Q, w ∈ A ∧ v ∈ A) → u < w) ↔ u < m (c v) := by
    constructor
    · intro h
      exact h (m (c v)) ((rel _ _).mpr (mc _))
    · intro h w hw
      exact lt_of_lt_of_le h (ml (c v) w ((rel w v).mp hw))
  have cardLT (a : Fin 3) : ((Finset.univ : Finset (Fin 3)).filter (fun b => b < a)).card = a.val := by
    fin_cases a <;> decide
  intro v
  change CanonColour Q v = _
  unfold CanonColour
  have filterEq :
      Finset.univ.filter (fun u : Fin 9 =>
        (∀ w : Fin 9, w < u → ¬ ∃ A ∈ Q, w ∈ A ∧ u ∈ A) ∧
          ∀ w : Fin 9, (∃ A ∈ Q, w ∈ A ∧ v ∈ A) → u < w) =
      ((Finset.univ : Finset (Fin 3)).filter (fun a => a < c v)).image m := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,minimum u,below u v,Finset.mem_image]
    constructor
    · rintro ⟨hu,huv⟩
      refine ⟨c u,?_,hu⟩
      rw [← hu] at huv
      exact (ord _ _).mp huv
    · rintro ⟨a,ha,heu⟩
      have hc : c u = a := heu ▸ mc a
      constructor
      · rw [hc]; exact heu
      · rw [← heu]; exact (ord _ _).mpr ha
  rw [filterEq,Finset.card_image_of_injective _ mi,cardLT]
