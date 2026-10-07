import SierksmaLean.Proofs.Proof_Sierksma_pl_orbit_move_multiple_three
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.pl_orbit_move_multiple_three :
    ∀ (x y : EngineParams)
    (hx : EngineGeneric x) (hy : EngineGeneric y) (hm : OneOrbitMove x y), ∀ j : Fin 3, (3 : ℤ) ∣ ConeCount x j-ConeCount y j :=
  @proof_Sierksma_pl_orbit_move_multiple_three
