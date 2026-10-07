import SierksmaLean.Proofs.Proof_Sierksma_FB_finite_core
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.finite_core :
    ∀ (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Sierksma.Universe 3) (hy : Sierksma.SignedSystem y)
    (hcard : (Sierksma.FB.idxSupp y).card ≤ 7), False :=
  @proof_Sierksma_FB_finite_core
