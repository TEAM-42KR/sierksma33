import SierksmaLean.Proofs.Proof_Sierksma_signed_relabel
import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
set_option autoImplicit false
open scoped BigOperators
open Common Sierksma
noncomputable section

theorem Sierksma.signed_relabel :
    ∀ (y : Common.Partition 9 → ZMod 3)
    (hy : SignedSystem y) (π : Equiv.Perm (Fin 9)), SignedSystem (fun Q => SplitSign π * y (Relabel π.symm Q)) ∧
      (Finset.univ.filter (fun Q : Common.Partition 9 =>
        SplitSign π * y (Relabel π.symm Q) ≠ 0)) =
        RelabelFamily π (Finset.univ.filter (fun Q : Common.Partition 9 => y Q ≠ 0)) :=
  @proof_Sierksma_signed_relabel
