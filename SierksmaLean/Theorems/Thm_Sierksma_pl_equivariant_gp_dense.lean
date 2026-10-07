import SierksmaLean.Proofs.Proof_Sierksma_pl_equivariant_gp_dense
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.pl_equivariant_gp_dense :
    Dense {x : EngineParams | EngineGeneric x} ∧ IsOpen {x : EngineParams | EngineGeneric x} ∧
    ∀ x y : EngineParams, EngineGeneric x → EngineGeneric y →
      ∃ m : ℕ, ∃ p : Fin (m+1) → EngineParams,
        p 0=x ∧ p (Fin.last m)=y ∧ (∀ i, EngineGeneric (p i)) ∧
        ∀ i : Fin m, OneOrbitMove (p i.castSucc) (p i.succ) :=
  @proof_Sierksma_pl_equivariant_gp_dense
