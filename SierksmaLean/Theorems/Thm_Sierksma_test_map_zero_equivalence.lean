import SierksmaLean.Proofs.Proof_Sierksma_test_map_zero_equivalence
import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open Common PLDegree Sierksma

theorem Sierksma.test_map_zero_equivalence :
    (∀ P : Config 9 3, ∀ A : Finset (Fin 9), ∀ col : Fin 9 → ZMod 3,
      ColoredZero P A col ↔ ColoredCommonHull P A col) ∧
    (∀ P : Config 9 3, StrongGP P → ∀ A : Finset (Fin 9), ∀ col : Fin 9 → ZMod 3,
      ColoredZero P A col → A=Finset.univ ∧ ColoredBlocks A col ∈ Universe 3) ∧
    (∀ P : Config 9 3, ∀ col : Fin 9 → ZMod 3,
      (∃ j : ZMod 3, 5 ≤ (ColorBlock Finset.univ col j).card) →
        (SignMatrix P col).det=0) ∧
    (∀ P ∈ GenericLocus, ∀ Q : Common.Partition 9,
      TverbergSign P Q ≠ 0 ↔ Q ∈ TverbergPartitions 3 P) :=
  @proof_Sierksma_test_map_zero_equivalence
