import SierksmaLean.Proofs.Proof_Sierksma_FB_k_normtab2_2
import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.k_normtab2_2 :
    Sierksma.FB.allR (fun j => !(Nat.testBit (Sierksma.FB.intt 36) j) || Nat.beq j (Sierksma.FB.R1.getD 2 0) || !(Nat.ble (Sierksma.FB.L1t (Sierksma.FB.R1.getD 2 0)) (Sierksma.FB.L1t j)) || (Sierksma.FB.validPerm (Sierksma.FB.n2 2 j) && Sierksma.FB.allR (fun f => Nat.beq (Sierksma.FB.tau1 (Sierksma.FB.epOf (Sierksma.FB.n2 2 j) f)) (Sierksma.FB.tau1 f)) 0 36 && Nat.beq (Sierksma.FB.relIdx (Sierksma.FB.n2 2 j) (Sierksma.FB.R1.getD 2 0)) (Sierksma.FB.R1.getD 2 0) && Nat.blt (Sierksma.FB.relIdx (Sierksma.FB.n2 2 j) j) 1855 && Nat.testBit (Sierksma.FB.rootBits 2) (Sierksma.FB.relIdx (Sierksma.FB.n2 2 j) j))) 0 1855 = true :=
  @proof_Sierksma_FB_k_normtab2_2
