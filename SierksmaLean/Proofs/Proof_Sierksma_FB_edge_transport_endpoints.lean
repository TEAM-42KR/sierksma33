import SierksmaLean.Definitions.Def_Sierksma_FBChecker
import SierksmaLean.Theorems.Thm_Sierksma_FB_edge_enumeration_spec
set_option autoImplicit false
open Sierksma.FB
set_option maxHeartbeats 500000

theorem proof_Sierksma_FB_edge_transport_endpoints (p : ℕ) (π : Equiv.Perm (Fin 9)) (hπ : ∀ v : Fin 9, (π v).val = pAt p v.val) :
 ∀ f < 36, epOf p f < 36 ∧
 ((eu (epOf p f) = pAt p (eu f) ∧ ev (epOf p f) = pAt p (ev f)) ∨
  (eu (epOf p f) = pAt p (ev f) ∧ ev (epOf p f) = pAt p (eu f))) := by
  intro f hf
  obtain ⟨huv,hv,hidx⟩ := edge_enumeration_spec.1 f hf
  have hu : eu f < 9 := lt_trans huv hv
  have hpu : pAt p (eu f) < 9 := by rw [← hπ ⟨eu f,hu⟩]; exact (π ⟨eu f,hu⟩).isLt
  have hpv : pAt p (ev f) < 9 := by rw [← hπ ⟨ev f,hv⟩]; exact (π ⟨ev f,hv⟩).isLt
  have hne : pAt p (eu f) ≠ pAt p (ev f) := by
    intro h
    have hh : π ⟨eu f,hu⟩ = π ⟨ev f,hv⟩ := Fin.ext (by simpa only [hπ] using h)
    have he := congrArg Fin.val (π.injective hh)
    exact (Nat.ne_of_lt huv) he
  have hf36 : Nat.beq f 36 = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh := Nat.eq_of_beq_eq_true h
    omega
  by_cases hlt : pAt p (eu f) < pAt p (ev f)
  · have h := edge_enumeration_spec.2 _ hpu _ hpv hlt
    have hep : epOf p f = eIdx (pAt p (eu f)) (pAt p (ev f)) := by
      have hb : Nat.blt (pAt p (eu f)) (pAt p (ev f)) = true := by simpa using hlt
      simp only [epOf,hf36,cond_false,hb,cond_true]
    rw [hep]
    exact ⟨h.1,Or.inl h.2⟩
  · have hgt : pAt p (ev f) < pAt p (eu f) := by omega
    have h := edge_enumeration_spec.2 _ hpv _ hpu hgt
    have hep : epOf p f = eIdx (pAt p (ev f)) (pAt p (eu f)) := by
      have hb : Nat.blt (pAt p (eu f)) (pAt p (ev f)) = false := by
        apply Bool.eq_false_iff.mpr
        simpa using hlt
      simp only [epOf,hf36,cond_false,hb]
    rw [hep]
    exact ⟨h.1,Or.inr h.2⟩
