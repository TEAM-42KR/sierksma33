import SierksmaLean.Definitions.Def_Sierksma_FBChecker
set_option autoImplicit false
open scoped BigOperators

theorem proof_Sierksma_FB_nine_list_bridge (c : ℕ → ℕ) :
    List.foldr (fun v acc => c v * 3 ^ v + acc) 0 (List.range 9) = (∑ v : Fin 9, c v.val * 3 ^ v.val) ∧
    ∀ a : ℕ, ((List.range 9).filter (fun v => Nat.beq (c v) a)).length =
      ((Finset.univ : Finset (Fin 9)).filter (fun v => c v.val = a)).card := by
  classical
  constructor
  · simp [List.range_succ,Fin.sum_univ_succ,Fin.succ]
    <;> omega
  · intro a
    have hj : ((Finset.univ : Finset (Fin 9)).filter (fun v => c v.val = a)).image Fin.val =
        (Finset.range 9).filter (fun v => c v = a) := by
      ext v
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_range]
      constructor
      · rintro ⟨u,hu,rfl⟩; exact ⟨u.isLt,hu⟩
      · rintro ⟨hv,hc⟩; exact ⟨⟨v,hv⟩,hc,rfl⟩
    have hh := Finset.card_image_of_injective
      ((Finset.univ : Finset (Fin 9)).filter (fun v => c v.val = a)) Fin.val_injective
    rw [hj] at hh
    rw [← hh, ← List.toFinset_card_of_nodup ((List.nodup_range (n := 9)).filter _)]
    congr 1
    ext v
    simp [List.toFinset_filter]
