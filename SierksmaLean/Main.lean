import SierksmaLean.Statement
import SierksmaLean.Theorems.Thm_Sierksma_main
import SierksmaLean.Theorems.Thm_Sierksma_public_iff

/-! # Head theorems (glue between the statements and the proof modules) -/

namespace SierksmaLean

theorem main_theorem : MainStatement := fun P => Sierksma.main P

theorem sierksma_three_three : PublicStatement := Sierksma.public_iff.mpr main_theorem

end SierksmaLean
