import SierksmaLean.Proofs.Proof_Sierksma_FB_k_c4lo
import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.k_c4lo :
    (Sierksma.FB.allR (fun x => List.any Sierksma.FB.c4W (fun g => !(Nat.testBit (Sierksma.FB.covOf g) x))) 0 1855 && List.all Sierksma.FB.c4W (fun g => Nat.blt g 76545 && Nat.beq (Nat.land (Sierksma.FB.covOf g) (Sierksma.FB.intt 35)) 0)) = true :=
  @proof_Sierksma_FB_k_c4lo
