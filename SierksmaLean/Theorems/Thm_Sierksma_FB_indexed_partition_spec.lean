import SierksmaLean.Proofs.Proof_Sierksma_FB_indexed_partition_spec
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.indexed_partition_spec :
    ∀ (i : ℕ) (hi : i < 1855), Sierksma.FB.partOf i ∈ Sierksma.Universe 3 ∧
    (∀ u v : Fin 9, (∃ A ∈ Sierksma.FB.partOf i, u ∈ A ∧ v ∈ A) ↔
      Sierksma.FB.colOf i u.val = Sierksma.FB.colOf i v.val) ∧
    (∀ v : Fin 9, Sierksma.CanonColour (Sierksma.FB.partOf i) v =
      ((Sierksma.FB.colOf i v.val : ℕ) : ZMod 3)) :=
  @proof_Sierksma_FB_indexed_partition_spec
