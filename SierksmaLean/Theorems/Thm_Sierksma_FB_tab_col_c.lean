import SierksmaLean.Proofs.Proof_Sierksma_FB_tab_col_c
import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false

theorem Sierksma.FB.tab_col_c :
    ∀ i < 1855, Sierksma.FB.idxOf
      (List.foldr (fun v acc => Sierksma.FB.colOf i v * 3 ^ v + acc) 0 (List.range 9)) = i :=
  @proof_Sierksma_FB_tab_col_c
