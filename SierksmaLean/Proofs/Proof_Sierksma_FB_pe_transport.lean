import SierksmaLean.Definitions.Def_Sierksma_FBChecker
import SierksmaLean.Theorems.Thm_Sierksma_FB_validPerm_equiv
import SierksmaLean.Theorems.Thm_Sierksma_FB_edge_enumeration_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_edge_transport_endpoints
import SierksmaLean.Theorems.Thm_Sierksma_FB_sharedBlock_relabel
import SierksmaLean.Theorems.Thm_Sierksma_FB_relIdx_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_indexed_partition_spec
import SierksmaLean.Theorems.Thm_Sierksma_FB_tab_intt
set_option autoImplicit false
open Common Sierksma Sierksma.FB
set_option maxHeartbeats 1000000

theorem proof_Sierksma_FB_pe_transport (p : ℕ) (hp : validPerm p = true) :
    (∀ f < 36, epOf p f < 36) ∧
    (∀ f < 36, ∀ g < 36, epOf p f = epOf p g → f = g) ∧
    (∀ j < 1855, relIdx p j < 1855) ∧
    (∀ j < 1855, ∀ f < 36, Nat.testBit (intt (epOf p f)) (relIdx p j) = Nat.testBit (intt f) j) := by
  classical
  obtain ⟨π,hπ⟩ := validPerm_equiv p hp
  have hrs := relIdx_spec π p hπ
  have hep := edge_transport_endpoints p π hπ
  have inj (a b : ℕ) (ha : a < 9) (hb : b < 9) (h : pAt p a = pAt p b) : a = b := by
    have hh : π ⟨a,ha⟩ = π ⟨b,hb⟩ := Fin.ext (by simpa only [hπ] using h)
    exact congrArg Fin.val (π.injective hh)
  refine ⟨fun f hf => (hep f hf).1,?_,fun j hj => (hrs.1 j hj).1,?_⟩
  · intro f hf g hg hfg
    obtain ⟨hfuv,hfv,hfi⟩ := edge_enumeration_spec.1 f hf
    obtain ⟨hguv,hgv,hgi⟩ := edge_enumeration_spec.1 g hg
    have hfu := lt_trans hfuv hfv
    have hgu := lt_trans hguv hgv
    have huu := congrArg eu hfg
    have hvv := congrArg ev hfg
    rcases (hep f hf).2 with hff | hff <;> rcases (hep g hg).2 with hgg | hgg
    · have he : eu f = eu g := inj _ _ hfu hgu (hff.1.symm.trans (huu.trans hgg.1))
      have hv : ev f = ev g := inj _ _ hfv hgv (hff.2.symm.trans (hvv.trans hgg.2))
      rw [← hfi,← hgi,he,hv]
    · have he : eu f = ev g := inj _ _ hfu hgv (hff.1.symm.trans (huu.trans hgg.1))
      have hv : ev f = eu g := inj _ _ hfv hgu (hff.2.symm.trans (hvv.trans hgg.2))
      omega
    · have he : ev f = eu g := inj _ _ hfv hgu (hff.1.symm.trans (huu.trans hgg.1))
      have hv : eu f = ev g := inj _ _ hfu hgv (hff.2.symm.trans (hvv.trans hgg.2))
      omega
    · have he : ev f = ev g := inj _ _ hfv hgv (hff.1.symm.trans (huu.trans hgg.1))
      have hv : eu f = eu g := inj _ _ hfu hgu (hff.2.symm.trans (hvv.trans hgg.2))
      rw [← hfi,← hgi,he,hv]
  · intro j hj f hf
    have hjr := (hrs.1 j hj).1
    have hfp := (hep f hf).1
    rw [tab_intt (relIdx p j) hjr (epOf p f) hfp,tab_intt j hj f hf]
    have hcv (u v : Fin 9) :
        colOf (relIdx p j) (pAt p u.val) = colOf (relIdx p j) (pAt p v.val) ↔
          colOf j u.val = colOf j v.val := by
      have hr := sharedBlock_relabel π (partOf j) u v
      rw [← (hrs.1 j hj).2,
        (indexed_partition_spec (relIdx p j) hjr).2.1 (π u) (π v),
        (indexed_partition_spec j hj).2.1 u v] at hr
      simpa only [hπ] using hr
    obtain ⟨huv,hv,_⟩ := edge_enumeration_spec.1 f hf
    have hu := lt_trans huv hv
    have h := hcv ⟨eu f,hu⟩ ⟨ev f,hv⟩
    apply Bool.eq_iff_iff.mpr
    rcases (hep f hf).2 with hh | hh
    · rw [hh.1,hh.2]
      simpa only [Nat.beq_eq] using h
    · rw [hh.1,hh.2]
      simpa only [Nat.beq_eq] using
        (eq_comm (a := colOf (relIdx p j) (pAt p (ev f)))
          (b := colOf (relIdx p j) (pAt p (eu f)))).trans h
