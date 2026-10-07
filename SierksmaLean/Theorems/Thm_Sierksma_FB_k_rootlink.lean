import SierksmaLean.Proofs.Proof_Sierksma_FB_k_rootlink
import SierksmaLean.Definitions.Def_Sierksma_FBUtil
import SierksmaLean.Definitions.Def_Sierksma_FBNormP
set_option autoImplicit false

theorem Sierksma.FB.k_rootlink :
    Sierksma.FB.allR (fun k => Sierksma.FB.allR (fun x => !(Nat.testBit (Sierksma.FB.rootBits k) x) || List.any (Sierksma.FB.rootList k) (fun r => Nat.beq r x)) 0 1855) 0 6 = true :=
  @proof_Sierksma_FB_k_rootlink
