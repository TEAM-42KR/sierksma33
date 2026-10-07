import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem proof_Sierksma_FB_k_normtab1 :
    Sierksma.FB.allR (fun j => !(Nat.testBit (Sierksma.FB.intt 36) j) || (Sierksma.FB.validPerm (Sierksma.FB.n1 j) && Sierksma.FB.allR (fun f => Nat.beq (Sierksma.FB.tau1 (Sierksma.FB.epOf (Sierksma.FB.n1 j) f)) (Sierksma.FB.tau1 f)) 0 36 && Sierksma.FB.anyR (fun k => Nat.beq (Sierksma.FB.relIdx (Sierksma.FB.n1 j) j) (Sierksma.FB.R1.getD k 0)) 0 6)) 0 1855 = true := by
  decide +kernel
