import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open Sierksma.FB
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem proof_Sierksma_FB_edge_enumeration_spec :
 (∀ f < 36, eu f < ev f ∧ ev f < 9 ∧ eIdx (eu f) (ev f) = f) ∧
 (∀ a < 9, ∀ b < 9, a < b → eIdx a b < 36 ∧ eu (eIdx a b) = a ∧ ev (eIdx a b) = b) := by
  have hf : ∀ f : Fin 36, eu f.val < ev f.val ∧ ev f.val < 9 ∧ eIdx (eu f.val) (ev f.val) = f.val := by decide
  have hab : ∀ a b : Fin 9, a.val < b.val → eIdx a.val b.val < 36 ∧
      eu (eIdx a.val b.val) = a.val ∧ ev (eIdx a.val b.val) = b.val := by decide
  exact ⟨fun f h => hf ⟨f,h⟩,fun a ha b hb h => hab ⟨a,ha⟩ ⟨b,hb⟩ h⟩
