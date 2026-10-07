import SierksmaLean.Definitions.Def_Sierksma_EngineParams
set_option autoImplicit false
open scoped BigOperators
open PLDegree Sierksma
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

private def signC {k : ℕ} (t : Fin k → ℕ) : ℤ :=
  (-1) ^ ((Finset.univ.filter (fun ij : Fin k × Fin k => ij.1 < ij.2 ∧ t ij.2 < t ij.1)).card)
private def rankC (s : Finset ℕ) (v : ℕ) : ℕ := (s.filter (fun w => w < v)).card
private def face (a : Fin 4 → Fin 6) : Finset ℕ := Finset.univ.image (HexTuple a)

private theorem signC_eq {k : ℕ} (t : Fin k → ℕ) : listSign t = signC t := by
  unfold listSign signC
  congr 2
  ext ij
  simp only [Finset.mem_filter]
private theorem rankC_eq (s : Finset ℕ) (v : ℕ) : rank s v = rankC s v := by
  unfold rank rankC
  congr 1
  ext w
  simp only [Finset.mem_filter]

private theorem listed_eq {k : ℕ} (t : Fin k → ℕ) :
    listedFace t = Finsupp.single (Finset.univ.image t) (signC t) := by
  unfold listedFace
  congr 1
  · ext v
    simp only [Finset.mem_image]
  · exact signC_eq t

private theorem inj (a : Fin 4 → Fin 6) : Function.Injective (HexTuple a) := by
  intro k l h
  have hk := k.isLt
  have hl := l.isLt
  have ha : ∀ i, (a i).val < 6 := fun i => (a i).isLt
  have hm1 := ha ⟨k.val/2, by omega⟩
  have hm2 := ha ⟨l.val/2, by omega⟩
  have hn1 := Nat.mod_lt ((a ⟨k.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hn2 := Nat.mod_lt ((a ⟨l.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hg : k.val / 2 = l.val / 2 := by
    simp only [HexTuple] at h
    split_ifs at h <;> omega
  have he : (⟨k.val/2, by omega⟩ : Fin 4) = ⟨l.val/2, by omega⟩ := Fin.ext hg
  simp only [HexTuple, he, hg] at h
  apply Fin.ext
  split_ifs at h <;> omega

private theorem face_card (a : Fin 4 → Fin 6) : (face a).card=8 := by
  rw [face, Finset.card_image_of_injective _ (inj a)]
  decide

private def boundaryHom : Chain ℕ →+ Chain ℕ where
  toFun c := boundary c
  map_zero' := by simp [boundary]
  map_add' c d := Finsupp.sum_add_index' (fun s => zero_smul ℤ (faceBoundary s))
    (fun s a b => add_smul a b (faceBoundary s))

private theorem facet_boundary (a : Fin 4 → Fin 6) :
    boundary (listedFace (HexTuple a)) =
      ∑ k : Fin 8, Finsupp.single ((face a).erase (HexTuple a k))
        (signC (HexTuple a) * (-1)^rankC (face a) (HexTuple a k)) := by
  rw [listed_eq, boundary, Finsupp.sum_single_index (by simp)]
  rw [faceBoundary, Finset.smul_sum]
  rw [Finset.sum_image (inj a).injOn]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finsupp.smul_single, smul_eq_mul, incidence, rankC_eq]
  congr 1
  ext v
  simp only [Finset.mem_erase, face]

private theorem support_face (s : Finset ℕ) (hs : s ∈ HexCycle.support) :
    ∃ a : Fin 4 → Fin 6, s = face a := by
  by_contra hn
  apply (Finsupp.mem_support_iff.mp hs)
  rw [HexCycle, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [listed_eq, Finsupp.single_apply, if_neg]
  intro he
  exact hn ⟨a, he.symm⟩

private theorem homogeneous : Homogeneous 8 HexCycle := by
  intro s hs
  obtain ⟨a, rfl⟩ := support_face s hs
  exact face_card a

private theorem orbit_arith (a : Fin 4 → Fin 6) (k l : Fin 8) :
    HexTuple a k < 24 ∧ ShiftVertex (HexTuple a k) ≠ HexTuple a l ∧
       ShiftVertex (ShiftVertex (HexTuple a k)) ≠ HexTuple a l := by
  have hk := k.isLt
  have hl := l.isLt
  have ha : ∀ i, (a i).val < 6 := fun i => (a i).isLt
  have hm1 := ha ⟨k.val/2, by omega⟩
  have hm2 := ha ⟨l.val/2, by omega⟩
  have hn1 := Nat.mod_lt ((a ⟨k.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hn2 := Nat.mod_lt ((a ⟨l.val/2, by omega⟩).val+1) (by omega : 0<6)
  have hbound : HexTuple a k < 24 := by
    dsimp [HexTuple]
    split_ifs <;> omega
  refine ⟨hbound, ?_, ?_⟩
  all_goals
    intro heq
    have hblock : k.val/2 = l.val/2 := by
      simp only [ShiftVertex, if_pos hbound, HexTuple] at heq
      split_ifs at heq <;> omega
    have hf : (⟨k.val/2, by omega⟩ : Fin 4) = ⟨l.val/2, by omega⟩ := Fin.ext hblock
    simp only [ShiftVertex, if_pos hbound, HexTuple, hf, hblock] at heq
    split_ifs at heq <;> omega

private theorem orbit_support : ∀ s ∈ HexCycle.support, ∀ v ∈ s,
    v<24 ∧ ShiftVertex v ∉ s ∧ ShiftVertex (ShiftVertex v) ∉ s := by
  intro s hs v hv
  obtain ⟨a, rfl⟩ := support_face s hs
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨(orbit_arith a k k).1, ?_, ?_⟩
  · intro h
    obtain ⟨l, _, heq⟩ := Finset.mem_image.mp h
    exact (orbit_arith a k l).2.1 heq.symm
  · intro h
    obtain ⟨l, _, heq⟩ := Finset.mem_image.mp h
    exact (orbit_arith a k l).2.2 heq.symm
private def bt (b : Fin 4 → Fin 2 → Fin 6) (k : Fin 8) : ℕ :=
  6*(k.val/2)+(b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).val
private theorem inversion (b : Fin 4 → Fin 2 → Fin 6) (k l : Fin 8) :
    (k < l ∧ bt b l < bt b k) ↔
      (k.val%2=0 ∧ l.val=k.val+1 ∧
       b ⟨k.val/2, by omega⟩ 1 < b ⟨k.val/2, by omega⟩ 0) := by
  have hk := k.isLt
  have hl := l.isLt
  have hbk := (b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).isLt
  have hbl := (b ⟨l.val/2, by omega⟩ ⟨l.val%2, by omega⟩).isLt
  constructor
  · intro ⟨h1,h2⟩
    have hi : k.val/2=l.val/2 := by dsimp [bt] at h2; omega
    have hp : k.val%2=0 ∧ l.val%2=1 ∧ l.val=k.val+1 := by omega
    refine ⟨hp.1,hp.2.2,?_⟩
    have he : (⟨l.val/2, by omega⟩ : Fin 4)=⟨k.val/2, by omega⟩ := Fin.ext hi.symm
    have ke : (⟨k.val%2, by omega⟩ : Fin 2)=0 := Fin.ext hp.1
    have le : (⟨l.val%2, by omega⟩ : Fin 2)=1 := Fin.ext hp.2.1
    dsimp [bt] at h2
    rw [he,ke,le] at h2
    omega
  · intro ⟨hp,he,hb⟩
    have hi : k.val/2=l.val/2 := by omega
    have hlp : l.val%2=1 := by omega
    have hfi : (⟨l.val/2, by omega⟩ : Fin 4)=⟨k.val/2, by omega⟩ := Fin.ext hi.symm
    have ke : (⟨k.val%2, by omega⟩ : Fin 2)=0 := Fin.ext hp
    have le : (⟨l.val%2, by omega⟩ : Fin 2)=1 := Fin.ext hlp
    refine ⟨by omega,?_⟩
    dsimp [bt]
    rw [hfi,ke,le]
    omega
private theorem sign_block (b : Fin 4 → Fin 2 → Fin 6) :
    signC (bt b) = ∏ i : Fin 4, (if b i 1 < b i 0 then (-1:ℤ) else 1) := by
  have hc : (Finset.univ.filter (fun ij : Fin 8 × Fin 8 =>
      ij.1 < ij.2 ∧ bt b ij.2 < bt b ij.1)).card =
      ∑ i : Fin 4, if b i 1 < b i 0 then 1 else 0 := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [inversion]
    rw [Fintype.sum_prod_type]
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    simp only [and_false, and_true, false_and, true_and, ite_false, ite_true,
      add_zero, zero_add]
    rfl
  unfold signC
  rw [hc]
  simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, pow_add]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, pow_zero, mul_one]
  split_ifs <;> norm_num

private def step (v : Fin 6) : Fin 6 := ⟨(v.val+1)%6, Nat.mod_lt _ (by omega)⟩
private def hb (a : Fin 4 → Fin 6) (i : Fin 4) (j : Fin 2) : Fin 6 :=
  if j=0 then a i else step (a i)
private theorem hex_bt (a : Fin 4 → Fin 6) : HexTuple a = bt (hb a) := by
  funext k
  dsimp [HexTuple, bt, hb, step]
  simp only [Fin.mk_eq_zero]
  split_ifs <;> rfl
private theorem step_lt (v : Fin 6) : step v < v ↔ v=5 := by
  have h := v.isLt
  simp only [step, Fin.lt_def, Fin.ext_iff]
  omega
private theorem sign_hex (a : Fin 4 → Fin 6) :
    signC (HexTuple a) = ∏ i : Fin 4, if a i=5 then (-1:ℤ) else 1 := by
  rw [hex_bt, sign_block]
  apply Finset.prod_congr rfl
  intro i _
  simp only [hb, Fin.reduceEq, ite_false, ite_true, step_lt]
private theorem block_less (b : Fin 4 → Fin 2 → Fin 6) (l k : Fin 8) :
    bt b l < bt b k ↔
      (l.val/2 < k.val/2 ∨ l.val/2=k.val/2 ∧
       b ⟨l.val/2, by omega⟩ ⟨l.val%2, by omega⟩ <
         b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩) := by
  have h1 := (b ⟨l.val/2, by omega⟩ ⟨l.val%2, by omega⟩).isLt
  have h2 := (b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).isLt
  simp only [bt, Fin.lt_def]
  omega
private def low (i : Fin 4) : Fin 8 := ⟨2*i.val, by omega⟩
private def high (i : Fin 4) : Fin 8 := ⟨2*i.val+1, by omega⟩
private theorem rank_as_sum (a : Fin 4 → Fin 6) (k : Fin 8) :
    rankC (face a) (HexTuple a k) =
      ∑ l : Fin 8, if HexTuple a l < HexTuple a k then 1 else 0 := by
  unfold rankC face
  rw [Finset.filter_image, Finset.card_image_of_injective _ (inj a)]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
private theorem rank_low (a : Fin 4 → Fin 6) (i : Fin 4) :
    rankC (face a) (HexTuple a (low i)) = 2*i.val + if a i=5 then 1 else 0 := by
  rw [rank_as_sum]
  simp_rw [hex_bt, block_less]
  fin_cases i <;>
    norm_num only [low, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, hb,
      Fin.mk_eq_zero, Fin.reduceEq, true_or, false_or, true_and, false_and,
      and_true, and_false, ite_true, ite_false, add_zero, zero_add]
  all_goals simp only [step_lt, lt_self_iff_false, ite_false, add_zero, zero_add]
  all_goals omega
private theorem step_gt (v : Fin 6) : v < step v ↔ v≠5 := by
  have h := v.isLt
  simp only [step, Fin.lt_def, Fin.ext_iff]
  omega
private theorem rank_high (a : Fin 4 → Fin 6) (i : Fin 4) :
    rankC (face a) (HexTuple a (high i)) = 2*i.val + if a i=5 then 0 else 1 := by
  rw [rank_as_sum]
  simp_rw [hex_bt, block_less]
  fin_cases i <;>
    norm_num only [high, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, hb,
      Fin.mk_eq_zero, Fin.reduceEq, true_or, false_or, true_and, false_and,
      and_true, and_false, ite_true, ite_false, add_zero, zero_add]
  all_goals simp only [step_gt, lt_self_iff_false, ite_false, add_zero, zero_add]
  all_goals split_ifs <;> omega

private def eps (v : Fin 6) : ℤ := if v=5 then -1 else 1
private def except (a : Fin 4 → Fin 6) (i : Fin 4) : ℤ :=
  ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, eps (a j)
private def coef (a : Fin 4 → Fin 6) (k : Fin 8) : ℤ :=
  signC (HexTuple a) * (-1)^rankC (face a) (HexTuple a k)
private theorem coef_low (a : Fin 4 → Fin 6) (i : Fin 4) :
    coef a (low i) = except a i := by
  unfold coef
  rw [sign_hex, rank_low, pow_add, pow_mul]
  norm_num
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  by_cases h : a i=5 <;> simp [eps, except, h]
private theorem coef_high (a : Fin 4 → Fin 6) (i : Fin 4) :
    coef a (high i) = -except a i := by
  unfold coef
  rw [sign_hex, rank_high, pow_add, pow_mul]
  norm_num
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  by_cases h : a i=5 <;> simp [eps, except, h]
private def stepE : Fin 6 ≃ Fin 6 where
  toFun := step
  invFun v := ⟨(v.val+5)%6, Nat.mod_lt _ (by omega)⟩
  left_inv v := by apply Fin.ext; have h := v.isLt; dsimp [step]; omega
  right_inv v := by apply Fin.ext; have h := v.isLt; dsimp [step]; omega
private def rotateAt (i : Fin 4) : (Fin 4 → Fin 6) ≃ (Fin 4 → Fin 6) :=
  Equiv.piCongrRight (fun j => if j=i then stepE else Equiv.refl (Fin 6))
private theorem rotate_apply (i j : Fin 4) (a : Fin 4 → Fin 6) :
    rotateAt i a j = if j=i then step (a j) else a j := by
  simp [rotateAt, Equiv.piCongrRight_apply]
  split_ifs <;> rfl
private theorem except_rotate (a : Fin 4 → Fin 6) (i : Fin 4) :
    except (rotateAt i a) i = except a i := by
  unfold except
  apply Finset.prod_congr rfl
  intro j hj
  rw [rotate_apply, if_neg (Finset.mem_erase.mp hj).1]
private theorem low_high_ne (i : Fin 4) : low i ≠ high i := by
  intro h
  have hv := congrArg Fin.val h
  change 2*i.val=2*i.val+1 at hv
  omega
private theorem rotate_tuple (a : Fin 4 → Fin 6) (i : Fin 4) (k : Fin 8)
    (hk : k≠high i) :
    HexTuple (rotateAt i a) k = HexTuple a (Equiv.swap (low i) (high i) k) := by
  fin_cases i <;> fin_cases k
  all_goals simp_all [HexTuple,rotate_apply,Equiv.swap_apply_def,high,low,step]
private theorem erase_pair (a : Fin 4 → Fin 6) (i : Fin 4) :
    (face a).erase (HexTuple a (low i)) =
      (face (rotateAt i a)).erase (HexTuple (rotateAt i a) (high i)) := by
  unfold face
  rw [← Finset.image_erase (inj a), ← Finset.image_erase (inj (rotateAt i a))]
  symm
  calc
    _ = ((Finset.univ.erase (high i)).image (Equiv.swap (low i) (high i))).image
        (HexTuple a) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro k hk
      exact rotate_tuple a i k (Finset.mem_erase.mp hk).1
    _ = _ := by
      rw [Finset.image_erase (Equiv.swap (low i) (high i)).injective,
        Finset.image_univ_of_surjective (Equiv.swap (low i) (high i)).surjective,
        Equiv.swap_apply_right]
private def term (a : Fin 4 → Fin 6) (k : Fin 8) : Chain ℕ :=
  Finsupp.single ((face a).erase (HexTuple a k)) (coef a k)
private theorem pair_term (a : Fin 4 → Fin 6) (i : Fin 4) :
    term a (low i) = -term (rotateAt i a) (high i) := by
  unfold term
  rw [coef_low,coef_high,except_rotate,erase_pair]
  simp
private theorem sum_split (f : Fin 8 → Chain ℕ) :
    (∑ k, f k) = ∑ i : Fin 4, (f (low i)+f (high i)) := by
  simp [Fin.sum_univ_succ,low,high]
  abel
private theorem cycle : IsCycle HexCycle := by
  change boundaryHom HexCycle=0
  rw [HexCycle, map_sum]
  change (∑ a : Fin 4 → Fin 6, boundary (listedFace (HexTuple a)))=0
  simp_rw [facet_boundary]
  change (∑ a : Fin 4 → Fin 6, ∑ k : Fin 8, term a k)=0
  simp_rw [sum_split]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_add_distrib]
  have hr : (∑ a : Fin 4 → Fin 6, term a (low i)) =
      -∑ a : Fin 4 → Fin 6, term a (high i) := by
    rw [← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv (rotateAt i) _ _ (fun a => pair_term a i)
  rw [hr]
  exact neg_add_cancel _

private def sb (a : Fin 4 → Fin 6) (i : Fin 4) (j : Fin 2) : Fin 6 :=
  if a i=5 then (if j=0 then 0 else 5) else hb a i j
private def sortedTuple (a : Fin 4 → Fin 6) : Fin 8 → ℕ := bt (sb a)
private theorem sb_increasing (a : Fin 4 → Fin 6) (i : Fin 4) : sb a i 0 < sb a i 1 := by
  by_cases h : a i=5
  · simp [sb,h]
  · simp [sb,h,hb,step_gt]
private theorem sorted_strict (a : Fin 4 → Fin 6) : StrictMono (sortedTuple a) := by
  intro k l hkl
  have hk := k.isLt
  have hl := l.isLt
  rw [sortedTuple,block_less]
  by_cases h : k.val/2=l.val/2
  · right
    have hp : k.val%2=0 ∧ l.val%2=1 := by omega
    have he : (⟨l.val/2, by omega⟩ : Fin 4)=⟨k.val/2, by omega⟩ := Fin.ext h.symm
    refine ⟨h,?_⟩
    have ke : (⟨k.val%2, by omega⟩ : Fin 2)=0 := Fin.ext hp.1
    have le : (⟨l.val%2, by omega⟩ : Fin 2)=1 := Fin.ext hp.2
    rw [he,ke,le]
    exact sb_increasing a _
  · left
    omega
private theorem sorted_image (a : Fin 4 → Fin 6) :
    Finset.univ.image (sortedTuple a) = face a := by
  ext w
  by_cases h0 : a 0=5 <;> by_cases h1 : a 1=5 <;>
    by_cases h2 : a 2=5 <;> by_cases h3 : a 3=5
  all_goals simp [Finset.mem_image,face,Fin.exists_fin_succ,sortedTuple,bt,sb,hb,
    HexTuple,step,h0,h1,h2,h3]
  all_goals tauto
private theorem sorted_emb (a : Fin 4 → Fin 6) :
    sortedTuple a = (face a).orderEmbOfFin (face_card a) := by
  apply Finset.orderEmbOfFin_unique (face_card a)
  · intro k
    rw [← sorted_image a]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  · exact sorted_strict a
private def relabelHom (f : ℕ → ℕ) : Chain ℕ →+ Chain ℕ where
  toFun c := relabel f c
  map_zero' := by simp [relabel]
  map_add' c d := Finsupp.sum_add_index'
    (fun s => zero_smul ℤ (listedFace (fun i : Fin s.card => f (s.orderEmbOfFin rfl i))))
    (fun s a b => add_smul a b _)
private theorem relabel_single (f : ℕ → ℕ) (s : Finset ℕ) (n : ℕ)
    (h : s.card=n) (c : ℤ) :
    relabel f (Finsupp.single s c) =
      c • listedFace (fun i : Fin n => f (s.orderEmbOfFin h i)) := by
  subst n
  rw [relabel,Finsupp.sum_single_index (by simp)]
private def two (v : Fin 6) : Fin 6 := ⟨(v.val+2)%6,Nat.mod_lt _ (by omega)⟩
private def twoE : Fin 6 ≃ Fin 6 where
  toFun := two
  invFun v := ⟨(v.val+4)%6,Nat.mod_lt _ (by omega)⟩
  left_inv v := by apply Fin.ext; have h := v.isLt; dsimp [two]; omega
  right_inv v := by apply Fin.ext; have h := v.isLt; dsimp [two]; omega
private def shiftAll : (Fin 4 → Fin 6) ≃ (Fin 4 → Fin 6) :=
  Equiv.piCongrRight (fun _ => twoE)
private theorem shiftAll_apply (a : Fin 4 → Fin 6) (i : Fin 4) : shiftAll a i = two (a i) := rfl
private def shiftedB (a : Fin 4 → Fin 6) (i : Fin 4) (j : Fin 2) : Fin 6 := two (sb a i j)
private theorem shift_block (b : Fin 4 → Fin 2 → Fin 6) :
    (fun k : Fin 8 => ShiftVertex (bt b k)) = bt (fun i j => two (b i j)) := by
  funext k
  have hk := k.isLt
  have hv := (b ⟨k.val/2, by omega⟩ ⟨k.val%2, by omega⟩).isLt
  have hx : bt b k < 24 := by dsimp [bt]; omega
  dsimp [bt,two]
  unfold ShiftVertex
  split_ifs <;> omega
private theorem shift_hex (a : Fin 4 → Fin 6) :
    (fun k : Fin 8 => ShiftVertex (HexTuple a k)) = HexTuple (shiftAll a) := by
  rw [hex_bt,shift_block,hex_bt]
  congr 1
  funext i j
  fin_cases j
  · simp [hb,shiftAll_apply]
  · simp only [hb,Fin.reduceEq,ite_false,shiftAll_apply]
    apply Fin.ext
    have h := (a i).isLt
    dsimp [step,two]
    omega
private theorem shifted_image (a : Fin 4 → Fin 6) :
    Finset.univ.image (fun k => ShiftVertex (sortedTuple a k)) = face (shiftAll a) := by
  calc
    _ = (Finset.univ.image (sortedTuple a)).image ShiftVertex :=
      (Finset.image_image (f := sortedTuple a) (g := ShiftVertex)
        (s := (Finset.univ : Finset (Fin 8)))).symm
    _ = _ := by
      rw [sorted_image,face,Finset.image_image]
      exact congrArg (fun f : Fin 8 → ℕ => Finset.univ.image f) (shift_hex a)
private theorem shift_sign_local : ∀ v : Fin 6,
    eps v * (if two (if v=5 then (5:Fin 6) else step v) <
      two (if v=5 then (0:Fin 6) else v) then (-1:ℤ) else 1) = eps (two v) := by
  decide +kernel
private theorem shifted_sign (a : Fin 4 → Fin 6) :
    signC (HexTuple a) * signC (fun k => ShiftVertex (sortedTuple a k)) =
      signC (HexTuple (shiftAll a)) := by
  rw [sign_hex]
  change (∏ i : Fin 4, eps (a i)) * signC (fun k => ShiftVertex (bt (sb a) k)) = _
  rw [shift_block,sign_block,sign_hex]
  change (∏ i : Fin 4, eps (a i)) *
      (∏ i : Fin 4, if two (sb a i 1) < two (sb a i 0) then (-1:ℤ) else 1) =
      ∏ i : Fin 4, eps (shiftAll a i)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [sb,hb,Fin.reduceEq,ite_false,ite_true,shiftAll_apply]
  exact shift_sign_local (a i)
private theorem relabel_facet (a : Fin 4 → Fin 6) :
    relabel ShiftVertex (listedFace (HexTuple a)) = listedFace (HexTuple (shiftAll a)) := by
  rw [listed_eq]
  change relabel ShiftVertex (Finsupp.single (face a) (signC (HexTuple a))) = _
  rw [relabel_single ShiftVertex (face a) 8 (face_card a)]
  rw [← sorted_emb a]
  rw [listed_eq,listed_eq,Finsupp.smul_single]
  rw [shifted_image]
  congr 1
  exact shifted_sign a
private theorem invariant : relabel ShiftVertex HexCycle=HexCycle := by
  change relabelHom ShiftVertex HexCycle=HexCycle
  rw [HexCycle,map_sum]
  change (∑ a : Fin 4 → Fin 6, relabel ShiftVertex (listedFace (HexTuple a))) =
    ∑ a : Fin 4 → Fin 6, listedFace (HexTuple a)
  exact Fintype.sum_equiv shiftAll _ _ relabel_facet

theorem proof_Sierksma_hexagon_join_cycle :
    Homogeneous 8 HexCycle ∧ IsCycle HexCycle ∧
    relabel ShiftVertex HexCycle=HexCycle ∧
    (∀ s ∈ HexCycle.support, ∀ v ∈ s, v<24 ∧ ShiftVertex v ∉ s ∧
      ShiftVertex (ShiftVertex v) ∉ s) := by
  exact ⟨homogeneous,cycle,invariant,orbit_support⟩
