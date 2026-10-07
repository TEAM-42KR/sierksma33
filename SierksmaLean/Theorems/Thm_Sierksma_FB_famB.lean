import SierksmaLean.Proofs.Proof_Sierksma_FB_famB
import SierksmaLean.Definitions.Def_Sierksma_FBNorm
set_option autoImplicit false

theorem Sierksma.FB.famB :
    ∀ k < 6, ∀ r2 ∈ Sierksma.FB.rootList k,
    Sierksma.FB.Good (Sierksma.FB.memBits (Sierksma.FB.pairSort (Sierksma.FB.R1.getD k 0) r2)) (Sierksma.FB.KS k r2) 5 (Sierksma.FB.capsOf 2 5) :=
  @proof_Sierksma_FB_famB
