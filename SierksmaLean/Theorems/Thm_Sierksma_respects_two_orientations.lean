import SierksmaLean.Proofs.Proof_Sierksma_respects_two_orientations
import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false

theorem Sierksma.respects_two_orientations :
    ∀ {n : ℕ} (Q : Common.Partition n) (c d : Fin n → ZMod 3) (hc : Sierksma.Respects Q c) (hd : Sierksma.Respects Q d) (u v : Fin n) (hne : c u ≠ c v), (∀ x y, d y - d x = c y - c x) ∨ (∀ x y, d y - d x = -(c y - c x)) :=
  @proof_Sierksma_respects_two_orientations
