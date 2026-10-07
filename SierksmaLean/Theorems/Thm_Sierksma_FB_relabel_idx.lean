import SierksmaLean.Proofs.Proof_Sierksma_FB_relabel_idx
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.relabel_idx :
    ∀ (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Sierksma.Universe 3) (hy : Sierksma.SignedSystem y)
    (p : ℕ) (hp : Sierksma.FB.validPerm p = true), ∃ y' : Common.Partition 9 → ZMod 3, Sierksma.SignedSystem y' ∧
      (∀ Q, y' Q ≠ 0 → Q ∈ Sierksma.Universe 3) ∧
      Sierksma.FB.idxSupp y' = (Sierksma.FB.idxSupp y).image (Sierksma.FB.relIdx p) :=
  @proof_Sierksma_FB_relabel_idx
