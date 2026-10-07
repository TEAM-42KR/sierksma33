import SierksmaLean.Proofs.Proof_Sierksma_FB_index_transfer
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.index_transfer :
    ∀ (y : Common.Partition 9 → ZMod 3)
    (hsupp : ∀ Q, y Q ≠ 0 → Q ∈ Sierksma.Universe 3) (hy : Sierksma.SignedSystem y), (Sierksma.FB.idxSupp y).card = ((Sierksma.Universe 3).filter (fun Q => y Q ≠ 0)).card ∧
      (∀ i ∈ Sierksma.FB.idxSupp y, i < 1855) ∧
      Sierksma.FB.signedIdx (Sierksma.FB.idxSupp y) ∧ Sierksma.FB.coversIdx (Sierksma.FB.idxSupp y) :=
  @proof_Sierksma_FB_index_transfer
