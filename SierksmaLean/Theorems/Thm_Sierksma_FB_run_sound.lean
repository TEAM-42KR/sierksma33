import SierksmaLean.Proofs.Proof_Sierksma_FB_run_sound
import SierksmaLean.Definitions.Def_Sierksma_FBRun
set_option autoImplicit false

theorem Sierksma.FB.run_sound :
    ∀ (s mem : List ℕ) (K b caps : ℕ) (ext : List (ℕ × ℕ × ℕ))
    (h : Sierksma.FB.runR s mem K b caps ext = true)
    (hext : ∀ e ∈ ext, Sierksma.FB.Good e.1 e.2.1 e.2.2 caps), Sierksma.FB.Good (Sierksma.FB.memBits mem) K b caps :=
  @proof_Sierksma_FB_run_sound
