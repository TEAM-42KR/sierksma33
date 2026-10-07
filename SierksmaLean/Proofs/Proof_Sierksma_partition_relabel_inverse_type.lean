import SierksmaLean.Definitions.Def_Sierksma_Covering
set_option autoImplicit false
open Sierksma

theorem proof_Sierksma_partition_relabel_inverse_type {n : ℕ}
    (p : Equiv.Perm (Fin n)) (Q : Common.Partition n) :
    Relabel p.symm (Relabel p Q) = Q ∧
      (Relabel p Q).val.map Finset.card = Q.val.map Finset.card := by
  classical
  have hinv (A : Common.Block n) : (A.image p).image p.symm = A := by
    simp [Finset.image_image, Function.comp_def]
  have hinj : Function.Injective (fun A : Common.Block n => A.image p) := by
    intro A B h
    have hh := congrArg (Finset.image p.symm) h
    simpa only [hinv] using hh
  have hcard (A : Common.Block n) : (A.image p).card = A.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => p.injective h)
  constructor
  · simp only [Relabel, Finset.image_image, Function.comp_def, hinv, Finset.image_id']
  · unfold Relabel
    rw [Finset.image_val_of_injOn (fun _ _ _ _ h => hinj h), Multiset.map_map]
    change Q.val.map (fun A => (A.image p).card) = Q.val.map Finset.card
    exact congrArg (fun f : Common.Block n → ℕ => Q.val.map f) (funext hcard)
