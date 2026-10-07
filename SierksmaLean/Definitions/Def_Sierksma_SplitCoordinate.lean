import SierksmaLean.Definitions.Def_Sierksma_SignedSystem
set_option autoImplicit false
noncomputable section
namespace Sierksma
def SplitCoordinate : (Fin 1 ⊕ (Fin 4 × Fin 2)) ≃ Fin 9 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) finProdFinEquiv).trans finSumFinEquiv
end Sierksma
