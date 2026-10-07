import SierksmaLean.Proofs.Proof_PLDegree_apex_independence
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem PLDegree.apex_independence :
    ∀ {V : Type*} [LinearOrder V] {n : ℕ}
    (hn : 1 ≤ n) (F : V → Fin n → ℝ) (z : Chain V) (s s' : V)
    (hz : Homogeneous n z) (hcycle : IsCycle z)
    (hs : Fresh s z) (hs' : Fresh s' z)
    (hg : ChainGP F (cone s z)) (hg' : ChainGP F (cone s' z)), signedCount F (cone s z)=signedCount F (cone s' z) :=
  @proof_PLDegree_apex_independence
