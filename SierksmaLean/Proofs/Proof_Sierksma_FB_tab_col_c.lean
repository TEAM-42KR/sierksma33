import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
set_option maxRecDepth 200000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

theorem proof_Sierksma_FB_tab_col_c :
    ∀ i < 1855, Sierksma.FB.idxOf
      (List.foldr (fun v acc => Sierksma.FB.colOf i v * 3 ^ v + acc) 0 (List.range 9)) = i := by
  decide +kernel
