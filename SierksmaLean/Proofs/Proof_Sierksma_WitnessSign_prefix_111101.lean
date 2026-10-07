import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Theorems.Thm_Sierksma_last_cofactor_certificate
set_option autoImplicit false
open Sierksma
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
theorem proof_Sierksma_WitnessSign_prefix_111101 : ∀ x y z : ZMod 3, (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,x,y,z] : Fin 9 → ZMod 3) v=j)).card ≤ 4) → (RQSignMatrix WitnessQ (![1,1,1,1,0,1,x,y,z] : Fin 9 → ZMod 3)).det ≠ 0 ∧ ∀ v, LastCofactorQ (RQSignMatrix WitnessQ (![1,1,1,1,0,1,x,y,z] : Fin 9 → ZMod 3)) v ≠ 0 := by
  intro x y z h
  fin_cases x <;> fin_cases y <;> fin_cases z
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,0,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,0,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,0,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,1,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,1,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,1,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,2,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,2,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,0,2,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,0,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,0,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,0,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,1,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,1,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,1,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,2,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,2,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,1,2,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,0,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,0,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,0,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,1,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,1,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,1,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,2,0] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,2,1] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
  · exact False.elim ((by decide +kernel : ¬ (∀ j : ZMod 3, (Finset.univ.filter (fun v => (![1,1,1,1,0,1,2,2,2] : Fin 9 → ZMod 3) v=j)).card ≤ 4)) h)
