import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_01
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_02
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_03
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_04
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_05
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_06
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_07
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_08
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_12
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_13
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_14
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_15
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_16
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_17
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_18
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_23
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_24
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_25
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_26
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_27
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_28
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_34
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_35
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_36
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_37
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_38
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_45
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_46
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_47
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_48
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_56
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_57
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_58
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_67
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_68
import SierksmaLean.Theorems.Thm_Sierksma_WitnessG4_edge_78
set_option autoImplicit false
open Sierksma
set_option maxHeartbeats 1000000
theorem proof_Sierksma_generic_witness_g4_sorted : ∀ e : Edge 9, e.1<e.2 → ∀ t t' : Fin 3 → Fin 9,
    StrictMono t → StrictMono t' →
    Disjoint (Endpoints e) (Finset.univ.image t) →
    Disjoint (Endpoints e) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly WitnessQ e t t' ≠ 0 := by
  have hf : ∀ u v : Fin 9, u<v → ∀ t t' : Fin 3 → Fin 9,
    StrictMono t → StrictMono t' →
    Disjoint (Endpoints ((u,v) : Edge 9)) (Finset.univ.image t) →
    Disjoint (Endpoints ((u,v) : Edge 9)) (Finset.univ.image t') →
    Disjoint (Finset.univ.image t) (Finset.univ.image t') → RQQPoly WitnessQ ((u,v) : Edge 9) t t' ≠ 0 := by
    intro u v h
    fin_cases u <;> fin_cases v
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_01
    · exact Sierksma.WitnessG4.edge_02
    · exact Sierksma.WitnessG4.edge_03
    · exact Sierksma.WitnessG4.edge_04
    · exact Sierksma.WitnessG4.edge_05
    · exact Sierksma.WitnessG4.edge_06
    · exact Sierksma.WitnessG4.edge_07
    · exact Sierksma.WitnessG4.edge_08
    · norm_num at h
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_12
    · exact Sierksma.WitnessG4.edge_13
    · exact Sierksma.WitnessG4.edge_14
    · exact Sierksma.WitnessG4.edge_15
    · exact Sierksma.WitnessG4.edge_16
    · exact Sierksma.WitnessG4.edge_17
    · exact Sierksma.WitnessG4.edge_18
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_23
    · exact Sierksma.WitnessG4.edge_24
    · exact Sierksma.WitnessG4.edge_25
    · exact Sierksma.WitnessG4.edge_26
    · exact Sierksma.WitnessG4.edge_27
    · exact Sierksma.WitnessG4.edge_28
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_34
    · exact Sierksma.WitnessG4.edge_35
    · exact Sierksma.WitnessG4.edge_36
    · exact Sierksma.WitnessG4.edge_37
    · exact Sierksma.WitnessG4.edge_38
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_45
    · exact Sierksma.WitnessG4.edge_46
    · exact Sierksma.WitnessG4.edge_47
    · exact Sierksma.WitnessG4.edge_48
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_56
    · exact Sierksma.WitnessG4.edge_57
    · exact Sierksma.WitnessG4.edge_58
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_67
    · exact Sierksma.WitnessG4.edge_68
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact Sierksma.WitnessG4.edge_78
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · norm_num at h
  intro e he
  exact hf e.1 e.2 he
