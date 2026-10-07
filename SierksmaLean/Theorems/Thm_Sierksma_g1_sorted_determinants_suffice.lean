import SierksmaLean.Proofs.Proof_Sierksma_g1_sorted_determinants_suffice
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open Sierksma

theorem Sierksma.g1_sorted_determinants_suffice :
    ∀ (P : RQConfig) (h : ∀ a : Fin 4 → Fin 9, StrictMono a → Matrix.det (fun i j : Fin 4 => RQLift P (a i) j.val) ≠ 0), ∀ a : Fin 4 → Fin 9, Function.Injective a → Matrix.det (fun i j : Fin 4 => RQLift P (a i) j.val) ≠ 0 :=
  @proof_Sierksma_g1_sorted_determinants_suffice
