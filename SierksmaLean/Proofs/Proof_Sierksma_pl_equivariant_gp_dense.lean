import SierksmaLean.Theorems.Thm_Sierksma_engine_generic_is_open
import SierksmaLean.Theorems.Thm_Sierksma_engine_generic_dense_of_witness
import SierksmaLean.Theorems.Thm_Sierksma_engine_generic_prefix_auxiliary
import SierksmaLean.Theorems.Thm_Sierksma_pl_model_count_one
set_option autoImplicit false
open PLDegree Sierksma
set_option maxHeartbeats 800000

theorem proof_Sierksma_pl_equivariant_gp_dense :
    Dense {x : EngineParams | EngineGeneric x} ∧ IsOpen {x : EngineParams | EngineGeneric x} ∧
    ∀ x y : EngineParams, EngineGeneric x → EngineGeneric y →
      ∃ m : ℕ, ∃ p : Fin (m+1) → EngineParams,
        p 0=x ∧ p (Fin.last m)=y ∧ (∀ i, EngineGeneric (p i)) ∧
        ∀ i : Fin m, OneOrbitMove (p i.castSucc) (p i.succ) := by
  classical
  refine ⟨Sierksma.engine_generic_dense_of_witness ModelParams
    Sierksma.pl_model_count_one.2.1, Sierksma.engine_generic_is_open, ?_⟩
  intro x y hx hy
  obtain ⟨z,hxg,hyg⟩ := Sierksma.engine_generic_prefix_auxiliary x y hx hy
  let p : Fin 20 → EngineParams := fun i =>
    if i.val≤9 then (fun r => if r.val < i.val then z r else x r)
    else (fun r => if r.val<19-i.val then z r else y r)
  have hx9 : (fun r : Fin 9 => if r.val<9 then z r else x r)=z := by
    funext r
    simp [r.isLt]
  have hy9 : (fun r : Fin 9 => if r.val<9 then z r else y r)=z := by
    funext r
    simp [r.isLt]
  refine ⟨19,p,?_,?_,?_,?_⟩
  · funext r
    simp [p]
  · funext r
    simp [p]
  · intro i
    by_cases hi : i.val≤9
    · simpa only [p,if_pos hi] using hxg ⟨i.val,by omega⟩
    · simpa only [p,if_neg hi] using hyg ⟨19-i.val,by omega⟩
  · intro i
    by_cases hi : i.val<9
    · refine ⟨⟨i.val,by omega⟩,?_⟩
      intro r hr
      have hne : r.val ≠ i.val := by
        intro he
        apply hr
        exact Fin.ext he
      have h1 : (i.castSucc : Fin 20).val≤9 := by simp; omega
      have h2 : (i.succ : Fin 20).val≤9 := by simp; omega
      have hiff : r.val < i.val ↔ r.val < i.val+1 := by omega
      dsimp only [p]
      rw [if_pos h1,if_pos h2]
      change (if r.val < i.val then z r else x r) =
        (if r.val < i.val+1 then z r else x r)
      exact if_congr hiff rfl rfl
    · by_cases hb : i.val=9
      · refine ⟨0,?_⟩
        intro r hr
        have h1 : (i.castSucc : Fin 20).val≤9 := by simp; omega
        have h2 : ¬(i.succ : Fin 20).val≤9 := by simp; omega
        simp only [p,if_pos h1,if_neg h2,Fin.val_castSucc,Fin.val_succ,hb]
        change (if r.val<9 then z r else x r) = (if r.val<9 then z r else y r)
        simp [r.isLt]
      · refine ⟨⟨18-i.val,by omega⟩,?_⟩
        intro r hr
        have hne : r.val ≠ 18-i.val := by
          intro he
          apply hr
          exact Fin.ext he
        have h1 : ¬(i.castSucc : Fin 20).val≤9 := by simp; omega
        have h2 : ¬(i.succ : Fin 20).val≤9 := by simp; omega
        have hiff : r.val<19-i.val ↔ r.val<19-(i.val+1) := by omega
        dsimp only [p]
        rw [if_neg h1,if_neg h2]
        change (if r.val<19-i.val then z r else y r) =
          (if r.val<19-(i.val+1) then z r else y r)
        exact if_congr hiff rfl rfl
