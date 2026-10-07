import SierksmaLean.Definitions.Def_Sierksma_EngineParams
import SierksmaLean.Definitions.Def_Common_TverbergPartitions
import SierksmaLean.Definitions.Def_Sierksma_Covering
import SierksmaLean.Definitions.Def_Sierksma_Amplification
import SierksmaLean.Definitions.Def_Sierksma_FractionalCover
import SierksmaLean.Definitions.Def_Sierksma_TwistedRealization
import SierksmaLean.Definitions.Def_PLDegree_Chain
section Reuse0
section Reuse0
section Reuse0
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

private theorem Sierksma.hexagon_join_cycle :
    Homogeneous 8 HexCycle ∧ IsCycle HexCycle ∧
    relabel ShiftVertex HexCycle=HexCycle ∧
    (∀ s ∈ HexCycle.support, ∀ v ∈ s, v<24 ∧ ShiftVertex v ∉ s ∧
      ShiftVertex (ShiftVertex v) ∉ s) := by
  exact ⟨homogeneous,cycle,invariant,orbit_support⟩
end
end Reuse0

section Reuse1
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open Common Sierksma

private theorem testW_shift_local (P : Config 9 3) (v : Fin 9) (j : ZMod 3) :
    R8 (TestW P v j) = TestW P v (j+1) := by
  ext k
  have hc : ∀ j : ZMod 3, j=0 ∨ j=1 ∨ j=2 := by decide +kernel
  rcases hc j with rfl | rfl | rfl <;> fin_cases k <;>
    simp +decide [R8,TestW] <;> ring

private theorem target_test_map_label_local (P : Config 9 3) (v : Fin 9) (j : ZMod 3) :
    TargetTestMap P (3*v.val+j.val) = TestW P v j := by
  have hj : j.val<3 := ZMod.val_lt j
  have hlt : 3*v.val+j.val<27 := by omega
  have hdiv : (3*v.val+j.val)/3=v.val := by omega
  have hmod : (3*v.val+j.val)%3=j.val := by omega
  simp [TargetTestMap,hlt,hdiv,hmod]

private theorem Sierksma.twist_test_coordinates (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (P : Config 9 3)
    (v : ℕ) (hv : v<27) :
    EngineMap (TestParams P pi c) v=TargetTestMap P (TwistPhi pi c v) := by
  have hp (k : ℕ) (u : Fin 9) (j : ZMod 3) :
      RPower k (TestW P u j)=TestW P u (j+k) := by
    unfold RPower
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,testW_shift_local]
      push_cast
      congr 1
      ring
  interval_cases v
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 0)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 0)) ((c 0-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 0)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 0)) ((c 0-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 0)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 0)) ((c 0-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 1)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 1)) ((c 1-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 1)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 1)) ((c 1-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 1)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 1)) ((c 1-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 2)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 2)) ((c 2-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 2)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 2)) ((c 2-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 2)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 2)) ((c 2-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 3)) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 3)) ((c 3-1+(0:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 3)) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 3)) ((c 3-1+(1:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosU 3)) (2 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi (SplitPosV 3)) ((c 3-1+(2:ZMod 3)) : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi 0) (0 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi 0) (1 : ZMod 3)).symm
  · simpa [EngineMap,TestParams,TwistPhi,SplitPosU,SplitPosV,Fin.coe_ofNat_eq_mod,hp,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] using
      (target_test_map_label_local P (pi 0) (2 : ZMod 3)).symm
end Reuse1

section Reuse2
open Common PLDegree Sierksma
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000

private def rawIndex (v : ℕ) : ℕ := if v<24 then 1+2*(v/6)+v%2 else 0

private theorem rawIndex_lt (v : ℕ) : rawIndex v<9 := by
  unfold rawIndex
  split_ifs <;> omega

private theorem rawIndex_orbit : ∀ v w : Fin 24, rawIndex v.val=rawIndex w.val →
    w.val=v.val ∨ w.val=ShiftVertex v.val ∨ w.val=ShiftVertex (ShiftVertex v.val) := by
  decide +kernel

theorem Sierksma.L14.test_map_facet_colouring (P : Config 9 3) (pi : Equiv.Perm (Fin 9))
    (c : Fin 4 → ZMod 3) (s : Finset ℕ) (hs : s ∈ (EngineCone 0).support) :
    s.card=9 ∧ ∃ f : s ↪ Fin 9, ∃ col : Fin 9 → ZMod 3,
      ∀ v : s, EngineMap (TestParams P pi c) v.val = TestW P (f v) (col (f v)) := by
  classical
  have hhex := Sierksma.hexagon_join_cycle
  have hexFresh : ∀ t ∈ HexCycle.support, (24:ℕ) ∉ t := by
    intro t ht h24
    have := (hhex.2.2.2 t ht 24 h24).1
    omega
  have hsupport : ∃ t ∈ HexCycle.support, s=insert 24 t := by
    by_contra hn
    apply (Finsupp.mem_support_iff.mp hs)
    simp only [EngineCone, Fin.val_zero, Nat.add_zero, cone, Finsupp.sum,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro t ht
    rw [faceCone, if_neg (hexFresh t ht)]
    rw [Finsupp.single_apply, if_neg]
    · simp
    · intro he
      have hde : (fun a b : ℕ => Classical.propDecidable (a=b)) =
          instDecidableEqNat := Subsingleton.elim _ _
      exact hn ⟨t,ht,by convert he.symm using 1 <;> ext u <;> simp⟩
  obtain ⟨t,ht,rfl⟩ := hsupport
  have hcard : (insert 24 t).card=9 := by
    rw [Finset.card_insert_of_notMem (hexFresh t ht), hhex.1 t ht]
  have hlt (v : ↥(insert 24 t)) : v.val<27 := by
    rcases Finset.mem_insert.mp v.property with h | h
    · omega
    · have := (hhex.2.2.2 t ht v.val h).1; omega
  have hinj : Function.Injective (fun v : ↥(insert 24 t) => rawIndex v.val) := by
    intro v w he
    rcases Finset.mem_insert.mp v.property with hv | hv
    · have he0 : rawIndex w.val=0 := by simpa [rawIndex,hv] using he.symm
      rcases Finset.mem_insert.mp w.property with hw | hw
      · exact Subtype.ext (hv.trans hw.symm)
      · have hwlt := (hhex.2.2.2 t ht w.val hw).1
        simp [rawIndex,hwlt] at he0
    · have hvlt := (hhex.2.2.2 t ht v.val hv).1
      rcases Finset.mem_insert.mp w.property with hw | hw
      · simp [rawIndex,hvlt,hw] at he
      · have hwlt := (hhex.2.2.2 t ht w.val hw).1
        rcases rawIndex_orbit ⟨v.val,hvlt⟩ ⟨w.val,hwlt⟩ he with h | h | h
        · exact Subtype.ext h.symm
        · exact False.elim ((hhex.2.2.2 t ht v.val hv).2.1 (h ▸ hw))
        · exact False.elim ((hhex.2.2.2 t ht v.val hv).2.2 (h ▸ hw))
  let f : ↥(insert 24 t) ↪ Fin 9 :=
    ⟨fun v => pi ⟨rawIndex v.val,rawIndex_lt v.val⟩, by
      intro v w he
      apply hinj
      exact congrArg Fin.val (pi.injective he)⟩
  have hphi (v : ↥(insert 24 t)) :
      TwistPhi pi c v.val < 27 ∧ (TwistPhi pi c v.val)/3 = (f v).val := by
    have hv := hlt v
    by_cases hv24 : v.val<24
    · let i : Fin 4 := ⟨v.val/6,by omega⟩
      by_cases heven : v.val%2=0
      · have he : (⟨rawIndex v.val,rawIndex_lt _⟩ : Fin 9)=SplitPosU i := by
          apply Fin.ext; simp [rawIndex,hv24,heven,SplitPosU,i]; omega
        have hp := (pi (SplitPosU i)).isLt
        have hmod : v.val%6/2<3 := by omega
        simp only [TwistPhi, dif_pos hv24, i, if_pos heven]
        have hf : f v = pi (SplitPosU i) := by change pi ⟨rawIndex v.val,rawIndex_lt _⟩=_; rw [he]
        rw [hf]
        dsimp only [i] at *
        constructor <;> omega
      · have hodd : v.val%2=1 := by omega
        have he : (⟨rawIndex v.val,rawIndex_lt _⟩ : Fin 9)=SplitPosV i := by
          apply Fin.ext; simp [rawIndex,hv24,hodd,SplitPosV,i]; omega
        have hp := (pi (SplitPosV i)).isLt
        have hm := ZMod.val_lt (c i-1+((v.val%6/2 : ℕ) : ZMod 3))
        simp only [TwistPhi, dif_pos hv24, i, if_neg heven]
        have hf : f v = pi (SplitPosV i) := by change pi ⟨rawIndex v.val,rawIndex_lt _⟩=_; rw [he]
        rw [hf]
        dsimp only [i] at *
        constructor <;> omega
    · have hv24eq : v.val=24 := by
        rcases Finset.mem_insert.mp v.property with he | he
        · exact he
        · have := (hhex.2.2.2 t ht v.val he).1; omega
      have hp := (pi 0).isLt
      simp [TwistPhi,hv24eq,f,rawIndex]
      omega
  let color (v : ↥(insert 24 t)) : ZMod 3 := ((TwistPhi pi c v.val)%3 : ℕ)
  let col := Function.extend f color (fun _ => 0)
  refine ⟨hcard,f,col,?_⟩
  intro v
  have hex := Sierksma.twist_test_coordinates pi c P v.val (hlt v)
  rw [hex]
  have hc : col (f v)=color v := f.injective.extend_apply color _ v
  rw [hc]
  simp only [TargetTestMap,dif_pos (hphi v).1]
  congr 2
  exact (hphi v).2
end Reuse2
end Reuse0

section Reuse1
set_option autoImplicit false
open Common Sierksma
open scoped BigOperators
set_option maxRecDepth 4000
private theorem Sierksma.classification (P : Config 9 3) (hP : StrongGP P) (Q : Common.Partition 9) (hQ : BlocksOn Q (Q.biUnion id)) (hcard : Q.card = 3) (hz : HasCommonHull P Q) : Q ∈ Universe 3 := by
  classical
  have hsupport (A : Block 9) (z : Fin 3 → ℝ) (hz : z ∈ convexHull ℝ (P '' (↑A : Set (Fin 9)))) : ∃ B : Block 9, B ⊆ A ∧ B.Nonempty ∧ B.card ≤ 4 ∧ z ∈ convexHull ℝ (P '' (↑B : Set (Fin 9))) := by
    rw [convexHull_eq_union] at hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨t, htA, htind, hzt⟩ := hz
    have hc : t.card ≤ 4 := by
      have h := htind.card_le_finrank_succ
      have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → (Fin 3 → ℝ))))
      have hdim3 : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
      simp only [Fintype.card_coe] at h
      omega
    have hx : ∀ x : t, ∃ i : Fin 9, i ∈ A ∧ P i = x := fun x => htA x.property
    choose g hgA hg using hx
    let B : Block 9 := Finset.univ.image g
    have himage : P '' (↑B : Set (Fin 9)) = (↑t : Set (Fin 3 → ℝ)) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hi
        rw [hg y]
        exact y.property
      · intro hx
        refine ⟨g ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩, hg ⟨x, hx⟩⟩
    have hzB : z ∈ convexHull ℝ (P '' (↑B : Set (Fin 9))) := by rwa [himage]
    refine ⟨B, ?_, ?_, ?_, hzB⟩
    · intro i hi
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hi
      exact hgA y
    · by_contra hn
      have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [he] at hzB
    · exact (Finset.card_image_le).trans (by simpa using hc)
  have hpair (A B : Block 9) (hd : Disjoint A B) (z : Fin 3 → ℝ)
      (ha : z ∈ convexHull ℝ (P '' (↑A : Set (Fin 9))))
      (hb : z ∈ convexHull ℝ (P '' (↑B : Set (Fin 9)))) : 5 ≤ A.card + B.card := by
    by_contra hn
    have hind := hP.1 (A ∪ B) (by rw [Finset.card_union_of_disjoint hd]; omega)
    let p : {i // i ∈ A ∪ B} → (Fin 3 → ℝ) := fun i => P i.val
    let s : Set {i // i ∈ A ∪ B} := {i | i.val ∈ A}
    let t : Set {i // i ∈ A ∪ B} := {i | i.val ∈ B}
    have hs : p '' s = P '' (↑A : Set (Fin 9)) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.val, hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, Finset.mem_union_left _ hi⟩, hi, rfl⟩
    have ht : p '' t = P '' (↑B : Set (Fin 9)) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.val, hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, Finset.mem_union_right _ hi⟩, hi, rfl⟩
    have ha' : z ∈ affineSpan ℝ (p '' s) := by
      rw [hs]
      exact convexHull_subset_affineSpan _ ha
    have hb' : z ∈ affineSpan ℝ (p '' t) := by
      rw [ht]
      exact convexHull_subset_affineSpan _ hb
    obtain ⟨i, hi, hj⟩ := hind.exists_mem_inter_of_exists_mem_inter_affineSpan ha' hb'
    exact Finset.disjoint_left.mp hd hi hj
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ ({a,b,c} : Common.Partition 9) := by simp
  have hb : b ∈ ({a,b,c} : Common.Partition 9) := by simp
  have hc : c ∈ ({a,b,c} : Common.Partition 9) := by simp
  have dab := hQ.2.1 a ha b hb hab
  have dac := hQ.2.1 a ha c hc hac
  have dbc := hQ.2.1 b hb c hc hbc
  obtain ⟨z,hz⟩ := hz
  obtain ⟨A,hAa,hAne,hA4,hzA⟩ := hsupport a z (hz a ha)
  obtain ⟨B,hBb,hBne,hB4,hzB⟩ := hsupport b z (hz b hb)
  obtain ⟨C,hCc,hCne,hC4,hzC⟩ := hsupport c z (hz c hc)
  have dAB : Disjoint A B := dab.mono hAa hBb
  have dAC : Disjoint A C := dac.mono hAa hCc
  have dBC : Disjoint B C := dbc.mono hBb hCc
  have hAB := hpair A B dAB z hzA hzB
  have hAC := hpair A C dAC z hzA hzC
  have hBC := hpair B C dBC z hzB hzC
  have hAz := convexHull_subset_affineSpan _ hzA
  have hBz := convexHull_subset_affineSpan _ hzB
  have hCz := convexHull_subset_affineSpan _ hzC
  have noA : ¬ (A.card = 2 ∧ B.card = 3 ∧ C.card = 3) := by
    rintro ⟨hA,hB,hC⟩
    exact hP.2 A B C hA hB hC dAB dAC dBC ⟨z,hAz,hBz,hCz⟩
  have noB : ¬ (B.card = 2 ∧ A.card = 3 ∧ C.card = 3) := by
    rintro ⟨hB,hA,hC⟩
    exact hP.2 B A C hB hA hC dAB.symm dBC dAC ⟨z,hBz,hAz,hCz⟩
  have noC : ¬ (C.card = 2 ∧ A.card = 3 ∧ B.card = 3) := by
    rintro ⟨hC,hA,hB⟩
    exact hP.2 C A B hC hA hB dAC.symm dBC.symm dAB ⟨z,hCz,hAz,hBz⟩
  have hA1 := Finset.card_pos.mpr hAne
  have hB1 := Finset.card_pos.mpr hBne
  have hC1 := Finset.card_pos.mpr hCne
  have hsum : 9 ≤ A.card + B.card + C.card := by omega
  have hUnionCard : (a ∪ b ∪ c).card = a.card + b.card + c.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dac,dbc⟩), Finset.card_union_of_disjoint dab]
  have hOrig : a.card + b.card + c.card ≤ 9 := by
    simpa only [hUnionCard, Fintype.card_fin] using Finset.card_le_univ (a ∪ b ∪ c)
  have hAaC := Finset.card_le_card hAa
  have hBbC := Finset.card_le_card hBb
  have hCcC := Finset.card_le_card hCc
  have ha4 : a.card ≤ 4 := by omega
  have hb4 : b.card ≤ 4 := by omega
  have hc4 : c.card ≤ 4 := by omega
  have hfull : ({a,b,c} : Common.Partition 9).biUnion id = Finset.univ := by
    have hh : a ∪ b ∪ c = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    simpa [Finset.biUnion_insert, Finset.union_assoc] using hh
  simp only [Universe, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨?_, hcard⟩, ?_⟩
  · rw [← hfull]
    exact hQ
  · intro D hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl
    · exact ha4
    · exact hb4
    · exact hc4

open scoped BigOperators
open Common Sierksma

private theorem Sierksma.L11.hull_weights (P : Config 9 3) (A : Finset (Fin 9)) (z : Fin 3 → ℝ) :
    z ∈ convexHull ℝ (P '' (A : Set (Fin 9))) ↔
    ∃ w : Fin 9 → ℝ, (∀ v, 0 ≤ w v) ∧ (∀ v, v ∉ A → w v = 0) ∧
      (∑ v, w v) = 1 ∧ (∑ v, w v • P v) = z := by
  classical
  let S : Set (Fin 3 → ℝ) := {z | ∃ w : Fin 9 → ℝ,
    (∀ v, 0 ≤ w v) ∧ (∀ v, v ∉ A → w v = 0) ∧
    (∑ v, w v) = 1 ∧ (∑ v, w v • P v) = z}
  have hS : Convex ℝ S := by
    rintro x ⟨u, hu, hus, hu1, rfl⟩ y ⟨w, hw, hws, hw1, rfl⟩ a b ha hb hab
    refine ⟨fun v => a * u v + b * w v, ?_, ?_, ?_, ?_⟩
    · intro v; exact add_nonneg (mul_nonneg ha (hu v)) (mul_nonneg hb (hw v))
    · intro v hv; simp [hus v hv, hws v hv]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hu1, hw1, hab]
    · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  constructor
  · apply convexHull_min _ hS
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨Pi.single v 1, ?_, ?_, ?_, ?_⟩
    · intro i; by_cases h : i = v <;> simp [h, Pi.single_apply]
    · intro i hi; have h : i ≠ v := by rintro rfl; exact hi hv
      simp [Pi.single_apply, h]
    · simp
    · simp
  · rintro ⟨w, hw, hws, hw1, rfl⟩
    have hs : ∑ v ∈ A, w v = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hws v hv)
    have heq : ∑ v ∈ A, w v • P v = ∑ v, w v • P v :=
      Finset.sum_subset (Finset.subset_univ _) (by intro v _ hv; simp [hws v hv])
    rw [← heq]
    exact (convex_convexHull ℝ _).sum_mem (fun v _ => hw v) hs
      (fun v hv => subset_convexHull ℝ _ ⟨v, hv, rfl⟩)

private theorem Sierksma.L11.zero_iff_common_hull (P : Config 9 3) (A : Finset (Fin 9)) (col : Fin 9 → ZMod 3) :
    ColoredZero P A col ↔ ColoredCommonHull P A col := by
  classical
  have colors : ∀ c : ZMod 3, c=0 ∨ c=1 ∨ c=2 := by decide
  have h01 : (0:ZMod 3) ≠ 1 := by decide
  have h02 : (0:ZMod 3) ≠ 2 := by decide
  have h12 : (1:ZMod 3) ≠ 2 := by decide
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h21 := Ne.symm h12
  let X (w : Fin 9 → ℝ) (j : ZMod 3) (k : Fin 4) :=
    ∑ v, if col v = j then w v * LiftCoord P v k.val else 0
  have row0 (v : Fin 9) (k : Fin 4) :
      TestW P v (col v) ⟨k.val, by omega⟩ =
        (if col v = 1 then LiftCoord P v k.val else 0) -
        (if col v = 0 then LiftCoord P v k.val else 0) := by
    rcases colors (col v) with hc | hc | hc <;> simp [TestW, k.isLt, hc, h01, h02, h12, h10, h20, h21]
  have row1 (v : Fin 9) (k : Fin 4) :
      TestW P v (col v) ⟨k.val + 4, by omega⟩ =
        (if col v = 2 then LiftCoord P v k.val else 0) -
        (if col v = 0 then LiftCoord P v k.val else 0) := by
    rcases colors (col v) with hc | hc | hc <;> simp [TestW, show ¬ k.val + 4 < 4 by omega, hc, h01, h02, h12, h10, h20, h21]
  have balance (w : Fin 9 → ℝ) :
      (∑ v, w v • TestW P v (col v)) = 0 ↔
        ∀ k : Fin 4, X w 1 k = X w 0 k ∧ X w 2 k = X w 0 k := by
    have eq0 (k : Fin 4) :
        (∑ v, w v • TestW P v (col v)) ⟨k.val, by omega⟩ = X w 1 k - X w 0 k := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row0, mul_sub,
        mul_ite, mul_zero, Finset.sum_sub_distrib, X]
    have eq1 (k : Fin 4) :
        (∑ v, w v • TestW P v (col v)) ⟨k.val + 4, by omega⟩ = X w 2 k - X w 0 k := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, row1, mul_sub,
        mul_ite, mul_zero, Finset.sum_sub_distrib, X]
    constructor
    · intro h k
      have h0 := congrFun h (⟨k.val, by omega⟩ : Fin 8)
      have h1 := congrFun h (⟨k.val + 4, by omega⟩ : Fin 8)
      rw [eq0] at h0; rw [eq1] at h1
      exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
    · intro h; funext k
      by_cases hk : k.val < 4
      · have he : k = (⟨k.val, by omega⟩ : Fin 8) := rfl
        rw [he, eq0 ⟨k.val,hk⟩, (h ⟨k.val, hk⟩).1, sub_self]; rfl
      · have he : k = (⟨(k.val-4)+4, by omega⟩ : Fin 8) := by apply Fin.ext; dsimp; omega
        rw [he, eq1 ⟨k.val-4, by omega⟩, (h ⟨k.val-4, by omega⟩).2, sub_self]; rfl
  constructor
  · rintro ⟨w, hw, hws, hw1, hw0⟩
    have hb := (balance w).mp hw0
    have htotal : X w 0 3 + X w 1 3 + X w 2 3 = 1 := by
      rw [← hw1]
      simp only [X, LiftCoord, show ¬ (3:ℕ) < 3 by omega, dif_neg, mul_one]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _; rcases colors (col v) with hc | hc | hc <;> simp [hc, h01, h02, h12, h10, h20, h21]
    have hm (j : ZMod 3) : X w j 3 = 1/3 := by
      have h := hb 3
      rcases colors j with rfl | rfl | rfl <;> linarith [h.1, h.2]
    let u (j : ZMod 3) (v : Fin 9) := if col v = j then 3*w v else 0
    have hu (j : ZMod 3) :
        (∀ v, 0 ≤ u j v) ∧ (∀ v, v ∉ ColorBlock A col j → u j v=0) ∧
        (∑ v, u j v)=1 ∧ (∑ v, u j v • P v) = (fun k : Fin 3 => 3*X w 0 k.castSucc) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v; dsimp [u]; split_ifs
        · exact mul_nonneg (by norm_num) (hw v)
        · exact le_rfl
      · intro v hv
        by_cases hc : col v = j
        · have hA : v ∉ A := by simpa [ColorBlock, hc] using hv
          simp [u, hc, hws v hA]
        · simp [u, hc]
      · have he : (∑ v, u j v) = 3*X w j 3 := by
          simp [u, X, LiftCoord, Finset.mul_sum, mul_ite]
        rw [he, hm]; norm_num
      · funext k
        have he : (∑ v, u j v • P v) k = 3*X w j k.castSucc := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u, X,
            LiftCoord, Fin.val_castSucc, k.isLt, dif_pos, ite_mul, zero_mul]
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl
          intro v _; split_ifs <;> ring
        rw [he]
        rcases colors j with rfl | rfl | rfl
        · rfl
        · rw [(hb k.castSucc).1]
        · rw [(hb k.castSucc).2]
    refine ⟨?_, ⟨fun k => 3*X w 0 k.castSucc, ?_⟩⟩
    · intro j
      by_contra hn
      have hempty : ColorBlock A col j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hz : ∀ v, u j v=0 := fun v => (hu j).2.1 v (by simp [hempty])
      have := (hu j).2.2.1
      simp [hz] at this
    · intro j; exact (Sierksma.L11.hull_weights P _ _).mpr ⟨u j, hu j⟩
  · rintro ⟨hne, z, hz⟩
    have hc : ∀ j : ZMod 3, ∃ u : Fin 9 → ℝ, (∀ v, 0 ≤ u v) ∧
        (∀ v, v ∉ ColorBlock A col j → u v=0) ∧ (∑ v, u v)=1 ∧ (∑ v, u v • P v)=z :=
      fun j => (Sierksma.L11.hull_weights P _ z).mp (hz j)
    choose u hu hus hu1 huz using hc
    have huoff (j : ZMod 3) (v : Fin 9) (h : col v ≠ j) : u j v=0 :=
      hus j v (by simp [ColorBlock, h])
    let w (v : Fin 9) := (u 0 v + u 1 v + u 2 v)/3
    have hx (j : ZMod 3) (k : Fin 4) :
        X w j k = (∑ v, u j v * LiftCoord P v k.val)/3 := by
      change (∑ v, if col v = j then w v * LiftCoord P v k.val else 0) = _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      dsimp [X, w]
      rcases colors j with rfl | rfl | rfl <;>
        rcases colors (col v) with hc | hc | hc <;>
        have off0 : col v ≠ 0 → u 0 v = 0 := huoff 0 v <;>
        have off1 : col v ≠ 1 → u 1 v = 0 := huoff 1 v <;>
        have off2 : col v ≠ 2 → u 2 v = 0 := huoff 2 v <;>
        simp [hc, h01, h02, h12, h10, h20, h21] at off0 off1 off2 ⊢ <;>
        simp_all only [add_zero, zero_add, zero_mul] <;> ring
    refine ⟨w, ?_, ?_, ?_, (balance w).mpr ?_⟩
    · intro v; dsimp [w]; exact div_nonneg (add_nonneg (add_nonneg (hu 0 v) (hu 1 v)) (hu 2 v)) (by norm_num)
    · intro v hv; simp [w, hus 0 v (by simp [ColorBlock, hv]),
        hus 1 v (by simp [ColorBlock, hv]), hus 2 v (by simp [ColorBlock, hv])]
    · dsimp [w]; rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
        hu1, hu1, hu1]; norm_num
    · intro k
      have he (j : ZMod 3) : (∑ v, u j v * LiftCoord P v k.val) =
          if h : k.val<3 then z ⟨k.val,h⟩ else 1 := by
        by_cases h : k.val<3
        · simpa [LiftCoord, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
            congrFun (huz j) ⟨k.val,h⟩
        · simp [LiftCoord, h, hu1]
      constructor <;> rw [hx, hx, he, he]

set_option maxHeartbeats 300000
set_option maxRecDepth 6000
open scoped BigOperators
open Common Sierksma

private theorem Sierksma.L11.face_exclusion (P : Config 9 3) (hP : StrongGP P) (A : Finset (Fin 9))
    (col : Fin 9 → ZMod 3) (hz : ColoredZero P A col) :
    A=Finset.univ ∧ ColoredBlocks A col ∈ Universe 3 := by
  classical
  obtain ⟨hne, z, hzh⟩ := (Sierksma.L11.zero_iff_common_hull P A col).mp hz
  have hQ : ColoredBlocks A col = Finset.univ.image (ColorBlock A col) := by
    apply Finset.filter_eq_self.mpr
    intro B hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact hne j
  have hmem (B : Finset (Fin 9)) : B ∈ ColoredBlocks A col ↔ ∃ j, B=ColorBlock A col j := by
    rw [hQ]; simp [eq_comm]
  have hunion : (ColoredBlocks A col).biUnion id = A := by
    ext v; simp only [Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨B, hB, hv⟩
      obtain ⟨j, rfl⟩ := (hmem B).mp hB
      exact (Finset.mem_filter.mp hv).1
    · intro hv
      refine ⟨ColorBlock A col (col v), (hmem _).mpr ⟨col v, rfl⟩, ?_⟩
      simp [ColorBlock, hv]
  have hinj : Function.Injective (ColorBlock A col) := by
    intro j k he
    obtain ⟨v, hv⟩ := hne j
    have hvk : v ∈ ColorBlock A col k := he ▸ hv
    exact (Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hvk).2
  have hcard : (ColoredBlocks A col).card=3 := by
    rw [hQ, Finset.card_image_of_injective _ hinj]
    norm_num
  have hbon : BlocksOn (ColoredBlocks A col) A := by
    refine ⟨?_, ?_, hunion⟩
    · intro B hB
      obtain ⟨j, rfl⟩ := (hmem B).mp hB
      exact ⟨hne j, Finset.filter_subset _ _⟩
    · intro B hB C hC hBC
      obtain ⟨j, rfl⟩ := (hmem B).mp hB
      obtain ⟨k, rfl⟩ := (hmem C).mp hC
      apply Finset.disjoint_left.mpr
      intro v hvj hvk
      have hjk : j=k := (Finset.mem_filter.mp hvj).2.symm.trans (Finset.mem_filter.mp hvk).2
      exact hBC (congrArg (ColorBlock A col) hjk)
  have hh : HasCommonHull P (ColoredBlocks A col) := by
    refine ⟨z, ?_⟩
    intro B hB; obtain ⟨j, rfl⟩ := (hmem B).mp hB; exact hzh j
  have hbon' : BlocksOn (ColoredBlocks A col) ((ColoredBlocks A col).biUnion id) := by
    rw [hunion]; exact hbon
  have hu := Sierksma.classification P hP (ColoredBlocks A col) hbon' hcard hh
  have hpu : IsPartition (ColoredBlocks A col) 3 := (Finset.mem_filter.mp hu).2.1
  exact ⟨hunion.symm.trans hpu.1.2.2, hu⟩
end Reuse1

section Reuse2
set_option autoImplicit false
open Common Sierksma
open scoped BigOperators

private theorem Sierksma.g1_polynomial_affine_gp (P : Config 9 3) (h : G1Polynomial P) : AffineGP P := by
  classical
  have h4 (a : Fin 4 → Fin 9) (ha : Function.Injective a) :
      AffineIndependent ℝ (fun i => P (a i)) := by
    let M : Matrix (Fin 4) (Fin 4) ℝ := fun i j => LiftCoord P (a i) j.val
    have hind : LinearIndependent ℝ (fun i => M i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero (h a ha)
    rw [affineIndependent_iff]
    intro s w hs hw
    have hm : ∑ i ∈ s, w i • M i = 0 := by
      ext j
      by_cases hj : j.val < 3
      · have he := congrFun hw ⟨j.val, hj⟩
        simpa [M, LiftCoord, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he
      · simpa [M, LiftCoord, hj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs
    exact (linearIndependent_iff'.mp hind) s w hm
  intro A hA
  obtain ⟨B, hAB, hBu, hB⟩ := Finset.exists_subsuperset_card_eq
    (show A ⊆ Finset.univ from Finset.subset_univ A) hA
    (show 4 ≤ (Finset.univ : Finset (Fin 9)).card by decide)
  let e : B ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using hB)
  let a : Fin 4 → Fin 9 := fun i => (e.symm i).val
  have ha : Function.Injective a := Subtype.val_injective.comp e.symm.injective
  have hBi : AffineIndependent ℝ (fun v : B => P v.val) := by
    convert (h4 a ha).comp_embedding e.toEmbedding using 1
    ext v
    simp [a, Function.comp_def]
  let f : A ↪ B := ⟨fun v => ⟨v.val, hAB v.property⟩, by
    intro v v' he
    exact Subtype.ext (congrArg (fun z : B => z.val) he)⟩
  exact hBi.comp_embedding f
end Reuse2

section Reuse3
set_option autoImplicit false
open Common Sierksma Set
open scoped BigOperators

private theorem Sierksma.generic_locus_strong_gp : ∀ P ∈ GenericLocus, StrongGP P := by
  classical
  intro P hP
  refine ⟨Sierksma.g1_polynomial_affine_gp P hP.1, ?_⟩
  have henumerate (T : Finset (Fin 9)) (hT : T.card = 3) :
      ∃ t : Fin 3 → Fin 9, Function.Injective t ∧ Finset.univ.image t = T := by
    let e : T ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hT)
    let t : Fin 3 → Fin 9 := fun i => (e.symm i).val
    refine ⟨t, Subtype.val_injective.comp e.symm.injective, ?_⟩
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (e.symm i).property
    · intro hv
      refine Finset.mem_image.mpr ⟨e ⟨v, hv⟩, Finset.mem_univ _, ?_⟩
      simp [t]
  have hcalc (t : Fin 3 → Fin 9) (q : Fin 3 → ℝ) : TripleDet P t q =
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 1-P (t 0) 1)*q 2 -
      (P (t 1) 0-P (t 0) 0)*(P (t 2) 2-P (t 0) 2)*q 1 -
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 0-P (t 0) 0)*q 2 +
      (P (t 1) 1-P (t 0) 1)*(P (t 2) 2-P (t 0) 2)*q 0 +
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 0-P (t 0) 0)*q 1 -
      (P (t 1) 2-P (t 0) 2)*(P (t 2) 1-P (t 0) 1)*q 0 := by
    change Matrix.det (Matrix.of ![P (t 1)-P (t 0), P (t 2)-P (t 0), q]) = _
    rw [Matrix.det_fin_three]
    simp [Matrix.of_apply, Matrix.vecTail, Matrix.vecHead, Pi.sub_apply]
  have hplane (t : Fin 3 → Fin 9) (z : Fin 3 → ℝ)
      (hz : z ∈ affineSpan ℝ (range (fun i => P (t i)))) :
      TripleDet P t (z-P (t 0)) = 0 := by
    let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := {
      toFun := fun q => TripleDet P t q
      map_add' := by
        intro q r
        simp only [hcalc, Pi.add_apply]
        ring
      map_smul' := by
        intro c q
        simp only [hcalc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    let F : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ :=
      L.toAffineMap - AffineMap.const ℝ (Fin 3 → ℝ) (L (P (t 0)))
    have hbase : ∀ i : Fin 3, F (P (t i)) = 0 := by
      intro i
      change L (P (t i)) - L (P (t 0)) = 0
      rw [← L.map_sub]
      change TripleDet P t (P (t i)-P (t 0)) = 0
      rw [hcalc]
      fin_cases i <;> simp [Pi.sub_apply] <;> ring
    have he : (range (fun i => P (t i))).EqOn F (AffineMap.const ℝ (Fin 3 → ℝ) 0) := by
      rintro x ⟨i, rfl⟩
      exact hbase i
    have hz' := AffineMap.eqOn_affineSpan he hz
    change L z - L (P (t 0)) = 0 at hz'
    rw [← L.map_sub] at hz'
    exact hz'
  intro E T T' hE hT hT' hET hET' hTT'
  rintro ⟨z, hzE, hzT, hzT'⟩
  have hep : ∃ u v : Fin 9, u < v ∧ E = {u,v} := by
    obtain ⟨u,v,hne,hEq⟩ := Finset.card_eq_two.mp hE
    rcases lt_or_gt_of_ne hne with huv | hvu
    · exact ⟨u,v,huv,hEq⟩
    · exact ⟨v,u,hvu,by simpa [Finset.pair_comm] using hEq⟩
  obtain ⟨u,v,huv,hEq⟩ := hep
  obtain ⟨t, ht, hti⟩ := henumerate T hT
  obtain ⟨t', ht', hti'⟩ := henumerate T' hT'
  let e : Edge 9 := (u,v)
  have hETt : Disjoint (Endpoints e) (Finset.univ.image t) := by
    simpa [e, Endpoints, hEq, hti] using hET
  have hETt' : Disjoint (Endpoints e) (Finset.univ.image t') := by
    simpa [e, Endpoints, hEq, hti'] using hET'
  have hTtt' : Disjoint (Finset.univ.image t) (Finset.univ.image t') := by
    simpa [hti,hti'] using hTT'
  have hQ : QPoly P e t t' ≠ 0 := hP.2.1 e huv t t' ht ht' hETt hETt' hTtt'
  have hTset (s : Fin 3 → Fin 9) (S : Finset (Fin 9)) (hi : Finset.univ.image s = S) :
      range (fun i => P (s i)) = P '' (S : Set (Fin 9)) := by
    rw [← hi]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i, rfl⟩
  have hzE' : z ∈ affineSpan ℝ ({P u,P v} : Set (Fin 3 → ℝ)) := by
    simpa only [hEq, Finset.coe_pair, Set.image_insert_eq, Set.image_singleton] using hzE
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp hzE'
  have hroot (s : Fin 3 → Fin 9)
      (hz : z ∈ affineSpan ℝ (range (fun i => P (s i)))) :
      r * TripleDet P s (P v-P u) + TripleDet P s (P u-P (s 0)) = 0 := by
    have hp := hplane s z hz
    have he : z-P (s 0) = r • (P v-P u) + (P u-P (s 0)) := by
      rw [← hr, AffineMap.lineMap_apply_module']
      abel
    rw [he] at hp
    simp only [hcalc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp ⊢
    linear_combination hp
  have hrT := hroot t (by rwa [hTset t T hti])
  have hrT' := hroot t' (by rwa [hTset t' T' hti'])
  apply hQ
  change TripleDet P t (P v-P u) * TripleDet P t' (P u-P (t' 0)) -
      TripleDet P t' (P v-P u) * TripleDet P t (P u-P (t 0)) = 0
  linear_combination (TripleDet P t (P v-P u))*hrT' -
    (TripleDet P t' (P v-P u))*hrT
end Reuse3

section Reuse4
set_option autoImplicit false
open scoped BigOperators
open Common

theorem Sierksma.block_hull_simplex (n d : ℕ) (P : Common.Config n d)
    (A : Common.Block n) (z : Fin d → ℝ) :
    z ∈ convexHull ℝ (P '' (↑A : Set (Fin n))) ↔
      ∃ w : stdSimplex ℝ A, (∑ v : A, (w.val v) • P v.val) = z := by
  classical
  let L : (A → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    ∑ v : A, (LinearMap.proj (R := ℝ) v).smulRight (P v.val)
  have hL (w : A → ℝ) : L w = ∑ v : A, w v • P v.val := by
    simp [L, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hbase : L '' Set.range (fun i j : A => if i = j then (1 : ℝ) else 0) =
      P '' (↑A : Set (Fin n)) := by
    have hb (i : A) : L (fun j : A => if i = j then (1 : ℝ) else 0) = P i.val := by
      rw [hL]
      simp [eq_comm]
    rw [← Set.range_comp']
    simp_rw [hb]
    exact (Set.image_eq_range P (↑A : Set (Fin n))).symm
  have himg : L '' stdSimplex ℝ A = convexHull ℝ (P '' (↑A : Set (Fin n))) := by
    rw [← convexHull_basis_eq_stdSimplex, L.image_convexHull, hbase]
  rw [← himg]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨⟨w, hw⟩, (hL w).symm.trans h⟩
  · rintro ⟨w, h⟩
    exact ⟨w.val, w.property, (hL w.val).trans h⟩
end Reuse4

section Reuse5
open Common PLDegree Sierksma
open scoped BigOperators
set_option maxHeartbeats 800000

theorem Sierksma.L14.test_map_no_boundary_zero (P : Config 9 3) (hP : P ∈ GenericLocus)
    (pi : Equiv.Perm (Fin 9)) (c : Fin 4 → ZMod 3) (s : Finset ℕ)
    (hs : s ∈ (EngineCone 0).support) :
    NoBoundaryZero (EngineMap (TestParams P pi c)) s := by
  classical
  obtain ⟨hcard, f, col, hrow⟩ := Sierksma.L14.test_map_facet_colouring P pi c s hs
  have hstrong := Sierksma.generic_locus_strong_gp P hP
  intro t ht hz
  let g : t ↪ Fin 9 := ⟨fun v => f ⟨v.val, ht.1 v.property⟩, by
    intro v w he
    apply Subtype.ext
    exact congrArg (fun z : s => z.val) (f.injective he)⟩
  let A := Finset.univ.image g
  have hcA : A.card=t.card := by
    dsimp only [A]
    rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_coe]
  have hsets : (fun v : Fin 9 => TestW P v (col v)) '' (A : Set (Fin 9)) =
      EngineMap (TestParams P pi c) '' (t : Set ℕ) := by
    ext y
    constructor
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hi
      exact ⟨v.val,v.property,hrow ⟨v.val,ht.1 v.property⟩⟩
    · rintro ⟨v,hv,rfl⟩
      refine ⟨g ⟨v,hv⟩, Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩, ?_⟩
      exact (hrow ⟨v,ht.1 hv⟩).symm
  have hzA : (0 : W8) ∈ convexHull ℝ ((fun v : Fin 9 => TestW P v (col v)) '' (A : Set (Fin 9))) := by
    rw [hsets]; exact hz
  obtain ⟨u,hu⟩ := (Sierksma.block_hull_simplex 9 8 (fun v => TestW P v (col v)) A 0).mp hzA
  let w : Fin 9 → ℝ := fun v => if hv : v ∈ A then u.val ⟨v,hv⟩ else 0
  have hw : ∀ v, 0 ≤ w v := by
    intro v; dsimp [w]; split_ifs
    · exact u.property.1 _
    · exact le_rfl
  have hws : ∀ v, v ∉ A → w v=0 := by intro v hv; simp [w,hv]
  have hsumA : ∑ v ∈ A, w v=1 := by
    rw [← Finset.sum_attach]
    simpa [w] using u.property.2
  have hsum : (∑ v, w v)=1 := by
    rw [← hsumA]
    symm
    exact Finset.sum_subset (Finset.subset_univ A) (fun v _ hv => hws v hv)
  have hreprA : ∑ v ∈ A, w v • TestW P v (col v)=0 := by
    rw [← Finset.sum_attach]
    simpa [w] using hu
  have hrepr : (∑ v, w v • TestW P v (col v))=0 := by
    rw [← hreprA]
    symm
    exact Finset.sum_subset (Finset.subset_univ A) (by intro v _ hv; rw [hws v hv,zero_smul])
  have hfull := (Sierksma.L11.face_exclusion P hstrong A col ⟨w,hw,hws,hsum,hrepr⟩).1
  have hlt : t.card < 9 := by simpa only [hcard] using Finset.card_lt_card ht
  have hAcard : A.card=9 := by rw [hfull]; simp
  omega
end Reuse5
end Reuse0

section Reuse1
open PLDegree Caratheodory
open scoped BigOperators
set_option maxHeartbeats 600000

theorem PLDegree.minimal_hull_affine_independent {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V)
    (h0 : (0 : Fin n → ℝ) ∈ hull F s) (hnb : NoBoundaryZero F s) :
    AffineIndependent ℝ (fun v : s => F v.val) := by
  classical
  have hinj : Function.Injective (fun v : s => F v.val) := by
    intro v w he
    by_contra hn
    have hvw : v.val ≠ w.val := fun h => hn (Subtype.ext h)
    have himg : F '' (s : Set V) = F '' ((s.erase v.val : Finset V) : Set V) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        by_cases huv : u = v.val
        · exact ⟨w.val, Finset.mem_erase.mpr ⟨Ne.symm hvw, w.property⟩, by simpa only [huv] using he.symm⟩
        · exact ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, rfl⟩
      · intro hy; exact Set.image_mono (Finset.erase_subset _ _) hy
    have hz : (0 : Fin n → ℝ) ∈ hull F (s.erase v.val) := by
      simpa only [hull, ← himg] using h0
    exact hnb _ (Finset.erase_ssubset v.property) hz
  let U := minCardFinsetOfMemConvexHull h0
  have hUsub : (U : Set (Fin n → ℝ)) ⊆ F '' (s : Set V) :=
    minCardFinsetOfMemConvexHull_subseteq h0
  have hUz : (0 : Fin n → ℝ) ∈ convexHull ℝ (U : Set (Fin n → ℝ)) :=
    mem_minCardFinsetOfMemConvexHull h0
  have hUai : AffineIndependent ℝ ((↑) : U → (Fin n → ℝ)) :=
    affineIndependent_minCardFinsetOfMemConvexHull h0
  let t := s.filter (fun v => F v ∈ U)
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hUt : (U : Set (Fin n → ℝ)) ⊆ F '' (t : Set V) := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := hUsub hy
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hy⟩, rfl⟩
  have htz : (0 : Fin n → ℝ) ∈ hull F t := (convexHull_mono hUt) hUz
  have he : t=s := by
    by_contra hn
    exact hnb t (Finset.ssubset_iff_subset_ne.mpr ⟨hts, hn⟩) htz
  have hmem (v : s) : F v.val ∈ U := by
    have ht : v.val ∈ t := by rw [he]; exact v.property
    exact (Finset.mem_filter.mp ht).2
  let e : s ↪ U := ⟨fun v => ⟨F v.val, hmem v⟩, by
    intro v w heq
    apply hinj
    exact congrArg Subtype.val heq⟩
  exact hUai.comp_embedding e
open scoped BigOperators
open PLDegree
set_option maxHeartbeats 1000000

section HullReuse
private theorem PLDegree.affine_coordinates_hull {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (hs : s.card=n+1)
    (hd : augmentedDet F s ≠ 0) (t : Finset V) (ht : t ⊆ s) (x : Fin n → ℝ) :
    let c := Matrix.vecMul (augment x 1) (augmentedMatrix F s hs)⁻¹
    x ∈ hull F t ↔ (∀ i, 0 ≤ c i) ∧
      (∀ i, s.orderEmbOfFin hs i ∉ t → c i = 0) := by
  classical
  let M := augmentedMatrix F s hs
  let e := s.orderEmbOfFin hs
  let c : (Fin n → ℝ) → Fin (n+1) → ℝ := fun y => Matrix.vecMul (augment y 1) M⁻¹
  change x ∈ hull F t ↔ (∀ i, 0 ≤ c x i) ∧ (∀ i, e i ∉ t → c x i = 0)
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (by simpa [augmentedDet, hs, M] using hd)
  have heq (y : Fin n → ℝ) : Matrix.vecMul (c y) M = augment y 1 := by
    dsimp [c]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M hM, Matrix.vecMul_one]
  have hsum (y : Fin n → ℝ) : ∑ i, c y i = 1 := by
    have hh := congrFun (heq y) (Fin.last n)
    simpa [M, Matrix.vecMul, dotProduct, augmentedMatrix, augment] using hh
  have hrepr (y : Fin n → ℝ) : ∑ i, c y i • F (e i) = y := by
    funext k
    have hh := congrFun (heq y) k.castSucc
    simpa [M, e, Matrix.vecMul, dotProduct, augmentedMatrix, augment,
      k.isLt, Finset.sum_apply, Pi.smul_apply] using hh
  have hvertex (j : Fin (n+1)) : c (F (e j)) = Pi.single j 1 := by
    have hj : augment (F (e j)) 1 = Matrix.vecMul (Pi.single j 1) M := by
      rw [Matrix.single_one_vecMul]
      rfl
    dsimp [c]
    rw [hj, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv M hM, Matrix.vecMul_one]
  have hccombo (y z : Fin n → ℝ) (r q : ℝ) (hrq : r+q=1) :
      c (r • y + q • z) = r • c y + q • c z := by
    have hau : augment (r • y + q • z) 1 = r • augment y 1 + q • augment z 1 := by
      funext j
      dsimp [augment]
      split_ifs with hj
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · simpa using hrq.symm
    dsimp [c]
    rw [hau, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul]
  constructor
  · intro hx
    let C : Set (Fin n → ℝ) := {y | (∀ i, 0 ≤ c y i) ∧ (∀ i, e i ∉ t → c y i = 0)}
    have hsub : F '' (t : Set V) ⊆ C := by
      rintro y ⟨v, hv, rfl⟩
      obtain ⟨j, hj⟩ : ∃ j, e j = v := by
        have hv' : v ∈ s := ht hv
        exact ⟨(s.orderIsoOfFin hs).symm ⟨v, hv'⟩, by simp [e, ← Finset.coe_orderIsoOfFin_apply]⟩
      subst v
      change (∀ i, 0 ≤ c (F (e j)) i) ∧ (∀ i, e i ∉ t → c (F (e j)) i = 0)
      rw [hvertex]
      constructor
      · intro i
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      · intro i hi
        have hne : i ≠ j := by intro hij; subst i; exact hi hv
        simp [Pi.single_apply, hne, Ne.symm hne]
    have hconv : Convex ℝ C := by
      intro y hy z hz r q hr hq hrq
      change (∀ i, 0 ≤ c (r • y + q • z) i) ∧
        (∀ i, e i ∉ t → c (r • y + q • z) i = 0)
      rw [hccombo y z r q hrq]
      exact ⟨fun i => add_nonneg (mul_nonneg hr (hy.1 i)) (mul_nonneg hq (hz.1 i)),
        fun i hi => by simp [Pi.add_apply, Pi.smul_apply, hy.2 i hi, hz.2 i hi]⟩
    exact convexHull_min hsub hconv hx
  · rintro ⟨hnonneg, hsupport⟩
    let I := Finset.univ.filter (fun i => e i ∈ t)
    have hIsum : ∑ i ∈ I, c x i = 1 := by
      rw [← hsum x]
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i _ hi
      exact hsupport i (by simpa [I] using hi)
    have hIrepr : ∑ i ∈ I, c x i • F (e i) = x := by
      calc
        ∑ i ∈ I, c x i • F (e i) = ∑ i, c x i • F (e i) := by
          apply Finset.sum_subset (Finset.subset_univ I)
          intro i _ hi
          rw [hsupport i (by simpa [I] using hi), zero_smul]
        _ = x := hrepr x
    have hcm := I.centerMass_mem_convexHull (fun i (_ : i ∈ I) => hnonneg i)
      (show 0 < ∑ i ∈ I, c x i by rw [hIsum]; norm_num)
      (fun i hi => Set.mem_image_of_mem F ((Finset.mem_filter.mp hi).2))
    simpa [hull, Finset.centerMass_eq_of_sum_1 _ _ hIsum, hIrepr] using hcm
end HullReuse

open PLDegree
open scoped BigOperators
set_option maxHeartbeats 600000

theorem PLDegree.minimal_hull_degree_data {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (hs : s.card=n+1)
    (h0 : (0 : Fin n → ℝ) ∈ hull F s) (hnb : NoBoundaryZero F s) :
    (augmentedMatrix F s hs).det ≠ 0 ∧ ∀ i, 0 < barycentric F s hs i := by
  classical
  have hai := PLDegree.minimal_hull_affine_independent F s h0 hnb
  let e : Fin (n+1) ↪ s := ⟨fun i => ⟨s.orderEmbOfFin hs i, s.orderEmbOfFin_mem hs i⟩,
    by intro i j he; exact (s.orderEmbOfFin hs).injective (congrArg Subtype.val he)⟩
  have hai' : AffineIndependent ℝ (fun i => F (s.orderEmbOfFin hs i)) := hai.comp_embedding e
  have hli : LinearIndependent ℝ (augmentedMatrix F s hs).row := by
    apply linearIndependent_iff'.mpr
    intro t w hw
    have hsum : ∑ i ∈ t, w i = 0 := by
      have hh := congrFun hw (Fin.last n)
      simpa [Matrix.row, augmentedMatrix, augment, Finset.sum_apply, Pi.smul_apply] using hh
    have hvec : ∑ i ∈ t, w i • F (s.orderEmbOfFin hs i) = 0 := by
      funext k
      have hh := congrFun hw k.castSucc
      simpa [Matrix.row, augmentedMatrix, augment, k.isLt, Finset.sum_apply, Pi.smul_apply] using hh
    exact hai'.eq_zero_of_sum_eq_zero hsum hvec
  have hd : (augmentedMatrix F s hs).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli))
  have hd' : augmentedDet F s ≠ 0 := by simpa [augmentedDet,hs] using hd
  have ha : augment (0 : Fin n → ℝ) 1 = originRow n := by
    funext j
    by_cases hj : j.val<n
    · have hjlast : j ≠ Fin.last n := by intro he; have := congrArg Fin.val he; simp at this; omega
      simp [augment,hj,originRow,Pi.single_apply,hjlast,Ne.symm hjlast]
    · have hjlast : j = Fin.last n := by apply Fin.ext; have := j.isLt; simp; omega
      subst j; simp [augment,originRow]
  have hnonneg : ∀ i, 0 ≤ barycentric F s hs i := by
    have hh := (PLDegree.affine_coordinates_hull F s hs hd' s (Finset.Subset.refl _) 0).mp h0
    simpa [barycentric,ha] using hh.1
  refine ⟨hd,?_⟩
  intro i
  by_contra hn
  have hi : barycentric F s hs i=0 := le_antisymm (le_of_not_gt hn) (hnonneg i)
  let v := s.orderEmbOfFin hs i
  have hz : (0 : Fin n → ℝ) ∈ hull F (s.erase v) := by
    apply (PLDegree.affine_coordinates_hull F s hs hd' (s.erase v) (Finset.erase_subset _ _) 0).mpr
    change (∀ j, 0 ≤ Matrix.vecMul (augment (0 : Fin n → ℝ) 1) (augmentedMatrix F s hs)⁻¹ j) ∧ _
    rw [ha]
    refine ⟨hnonneg,?_⟩
    intro j hj
    have hjv : s.orderEmbOfFin hs j=v := by
      by_contra hjv
      exact hj (Finset.mem_erase.mpr ⟨hjv,s.orderEmbOfFin_mem hs j⟩)
    have hji : j=i := (s.orderEmbOfFin hs).injective hjv
    subst j
    exact hi
  exact hnb _ (Finset.erase_ssubset (s.orderEmbOfFin_mem hs i)) hz
end Reuse1

section Reuse2
open PLDegree Filter
open scoped Topology BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem PLDegree.simplex_degree_locally_constant {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (hs : s.card=n+1)
    (hd : (augmentedMatrix F s hs).det ≠ 0) (hb : ∀ i, barycentric F s hs i ≠ 0) :
    ∀ᶠ G in nhds F, simplexDegree G s=simplexDegree F s := by
  classical
  have hM : Continuous (fun G : V → Fin n → ℝ => augmentedMatrix G s hs) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    unfold augmentedMatrix augment
    split_ifs <;> fun_prop
  have hdet : ContinuousAt (fun G : V → Fin n → ℝ => (augmentedMatrix G s hs).det) F := hM.matrix_det.continuousAt
  have hinv : ContinuousAt (fun G : V → Fin n → ℝ => (augmentedMatrix G s hs)⁻¹) F := by
    apply (continuousAt_matrix_inv (augmentedMatrix F s hs) _).comp hM.continuousAt
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd)
  have hbar (i : Fin (n+1)) : ContinuousAt (fun G => barycentric G s hs i) F := by
    unfold barycentric Matrix.vecMul dotProduct
    apply tendsto_finsetSum
    intro j hj
    exact continuousAt_const.mul
      ((continuous_apply i).continuousAt.comp ((continuous_apply j).continuousAt.comp hinv))
  have hpos (i : Fin (n+1)) : ∀ᶠ G in nhds F,
      (0 < barycentric G s hs i ↔ 0 < barycentric F s hs i) := by
    rcases (hb i).lt_or_gt with hn | hp
    · filter_upwards [(hbar i).tendsto.eventually_lt_const hn] with G hG
      simp [hn.not_gt,hG.not_gt]
    · filter_upwards [(hbar i).tendsto.eventually_const_lt hp] with G hG
      simp [hp,hG]
  have hsign : ∀ᶠ G in nhds F,
      SignType.sign (augmentedMatrix G s hs).det=SignType.sign (augmentedMatrix F s hs).det := by
    rcases hd.lt_or_gt with hn | hp
    · filter_upwards [hdet.tendsto.eventually_lt_const hn] with G hG
      rw [sign_neg hG,sign_neg hn]
    · filter_upwards [hdet.tendsto.eventually_const_lt hp] with G hG
      rw [sign_pos hG,sign_pos hp]
  filter_upwards [hdet.eventually_ne hd,Filter.eventually_all.2 hpos,hsign] with G hG hp hsgn
  have hpall : (∀ i, 0 < barycentric G s hs i) ↔ (∀ i, 0 < barycentric F s hs i) := forall_congr' hp
  have heq : (fun a b : Fin (n+1) => Classical.propDecidable (a=b)) =
      (inferInstance : DecidableEq (Fin (n+1))) := Subsingleton.elim _ _
  simp only [simplexDegree,dif_pos hs,heq,hG,hd,true_and,hpall,hsgn]
  congr 2 <;> simp_all
end Reuse2

section Reuse3
open Common PLDegree Sierksma
open scoped BigOperators

private theorem finite_hull_zero_closed_local {V : Type*} [LinearOrder V] {n : ℕ} (s : Finset V) :
    IsClosed {F : V → Fin n → ℝ | (0 : Fin n → ℝ) ∈ hull F s} := by
  classical
  let W := stdSimplex ℝ s
  let f : (V → Fin n → ℝ) × W → (Fin n → ℝ) :=
    fun p => ∑ i : s, p.2.val i • p.1 i
  have hc : Continuous f := by
    apply continuous_finset_sum
    intro i hi
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
      ((continuous_apply i.val).comp continuous_fst)
  have he : ∀ F : V → Fin n → ℝ,
      (0 : Fin n → ℝ) ∈ hull F s ↔ ∃ w : W, f (F,w)=0 := by
    intro F
    let L : (s → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      ∑ i : s, (LinearMap.proj (R := ℝ) i).smulRight (F i)
    have hL : ∀ w : s → ℝ, L w = ∑ i : s, w i • F i := by
      intro w
      simp [L]
    have hr : (fun i : s => L (Pi.single i 1)) = fun i : s => F i := by
      funext i
      rw [hL]
      simp [Pi.single_apply]
    have hh : hull F s = L '' stdSimplex ℝ s := by
      rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull,
        ← Set.range_comp]
      change convexHull ℝ (F '' (s : Set V)) = convexHull ℝ (Set.range _)
      rw [show (L ∘ (fun i : s => Pi.single i (1 : ℝ))) =
          (fun i : s => F i) from hr]
      congr 1
      ext v
      simp
    rw [hh]
    constructor
    · rintro ⟨w, hw, hzero⟩
      exact ⟨⟨w,hw⟩, (hL w).symm.trans hzero⟩
    · rintro ⟨w, hw⟩
      exact ⟨w.val,w.property,(hL w.val).trans hw⟩
  have himg : {F : V → Fin n → ℝ | (0 : Fin n → ℝ) ∈ hull F s} =
      Prod.fst '' {p : (V → Fin n → ℝ) × W | f p=0} := by
    ext F
    simp only [Set.mem_setOf_eq, Set.mem_image, he]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨(F,w),hw,rfl⟩
    · rintro ⟨⟨F',w⟩,hw,hF⟩
      change F'=F at hF
      subst F'
      exact ⟨w,hw⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ (isClosed_eq hc continuous_const)

private theorem simplex_degree_nonzero_mem_hull_local {V : Type*} [LinearOrder V] {n : ℕ}
    (F : V → Fin n → ℝ) (s : Finset V) (h : simplexDegree F s ≠ 0) :
    (0 : Fin n → ℝ) ∈ hull F s := by
  classical
  unfold simplexDegree at h
  split_ifs at h with hs hm
  · let w := barycentric F s hs
    have heq : Matrix.vecMul w (augmentedMatrix F s hs) = originRow n := by
      dsimp [w, barycentric]
      rw [Matrix.vecMul_vecMul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hm.1), Matrix.vecMul_one]
    have hsum : ∑ i, w i = 1 := by
      have hh := congrFun heq (Fin.last n)
      simpa [Matrix.vecMul, dotProduct, augmentedMatrix, augment, originRow] using hh
    have hz : ∑ i, w i • F (s.orderEmbOfFin hs i) = (0 : Fin n → ℝ) := by
      funext k
      have hh := congrFun heq k.castSucc
      simpa [Matrix.vecMul, dotProduct, augmentedMatrix, augment, originRow,
        k.isLt, Fin.castSucc_ne_last, Finset.sum_apply, Pi.smul_apply] using hh
    apply mem_convexHull_of_exists_fintype w (fun i => F (s.orderEmbOfFin hs i))
      (fun i => (hm.2 i).le) hsum _ hz
    intro i
    exact Set.mem_image_of_mem _ (s.orderEmbOfFin_mem hs i)
  · exact (h rfl).elim
  · exact (h rfl).elim

private theorem engine_map_continuous_local : Continuous (EngineMap : EngineParams → ℕ → W8) := by
  have hR : Continuous R8 := by
    apply continuous_pi
    intro j
    unfold R8
    split_ifs <;> fun_prop
  apply continuous_pi
  intro v
  unfold EngineMap
  split_ifs
  · exact (hR.iterate (v%6/2)).comp (continuous_apply _)
  · exact (hR.iterate (v-24)).comp (continuous_apply _)
  · exact continuous_const

theorem Sierksma.zero_free_facet_stability (x : EngineParams) (s : Finset ℕ)
    (hs : (0 : W8) ∉ PLDegree.hull (EngineMap x) s) :
    ∃ delta : ℝ, 0<delta ∧ ∀ y : EngineParams,
      CloseParams y x delta → PLDegree.simplexDegree (EngineMap y) s=0 := by
  have hclosed : IsClosed {z : EngineParams | (0 : W8) ∈ hull (EngineMap z) s} :=
    (finite_hull_zero_closed_local s).preimage engine_map_continuous_local
  obtain ⟨delta,hdelta,hball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl x hs
  refine ⟨delta,hdelta,?_⟩
  intro y hy
  have hd : dist y x<delta := by
    apply (dist_pi_lt_iff hdelta).2
    intro i
    apply (dist_pi_lt_iff hdelta).2
    intro j
    simpa only [Real.dist_eq] using hy i j
  have hmiss : (0 : W8) ∉ hull (EngineMap y) s := hball hd
  by_contra hn
  exact hmiss (simplex_degree_nonzero_mem_hull_local (EngineMap y) s hn)
end Reuse3

section Reuse4
open Common Sierksma

theorem Sierksma.engine_map_continuous : Continuous (EngineMap : EngineParams → ℕ → W8) := by
  have hR : Continuous R8 := by
    apply continuous_pi
    intro j
    unfold R8
    split_ifs <;> fun_prop
  apply continuous_pi
  intro v
  unfold EngineMap
  split_ifs
  · exact (hR.iterate (v%6/2)).comp (continuous_apply _)
  · exact (hR.iterate (v-24)).comp (continuous_apply _)
  · exact continuous_const
end Reuse4

section Reuse5
open Common PLDegree Sierksma Filter
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000

theorem proof_Sierksma_test_map_degree_stability (P : Config 9 3) (hP : P ∈ GenericLocus)
    (pi : Equiv.Perm (Fin 9)) (hpi : IsSplitting pi) (c : Fin 4 → ZMod 3) :
    ∃ delta : ℝ, 0<delta ∧ ∀ x : EngineParams,
      CloseParams x (TestParams P pi c) delta → ∀ s ∈ (EngineCone 0).support,
      simplexDegree (EngineMap x) s=simplexDegree (EngineMap (TestParams P pi c)) s := by
  classical
  let x0 := TestParams P pi c
  let A := (EngineCone 0).support
  have heach (s : A) : ∀ᶠ x in nhds x0,
      simplexDegree (EngineMap x) s.val = simplexDegree (EngineMap x0) s.val := by
    by_cases hz : (0 : W8) ∈ hull (EngineMap x0) s.val
    · have hs : s.val.card=8+1 := (Sierksma.L14.test_map_facet_colouring P pi c s.val s.property).1
      have hnb := Sierksma.L14.test_map_no_boundary_zero P hP pi c s.val s.property
      obtain ⟨hd,hpos⟩ := PLDegree.minimal_hull_degree_data (EngineMap x0) s.val hs hz hnb
      have hb : ∀ i, barycentric (EngineMap x0) s.val hs i ≠ 0 := fun i => ne_of_gt (hpos i)
      have hloc := PLDegree.simplex_degree_locally_constant (EngineMap x0) s.val hs hd hb
      exact Sierksma.engine_map_continuous.continuousAt.tendsto.eventually hloc
    · obtain ⟨delta,hdelta,hzero⟩ := Sierksma.zero_free_facet_stability x0 s.val hz
      have hself : CloseParams x0 x0 delta := by intro i j; simpa using hdelta
      have hdeg0 := hzero x0 hself
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨delta,hdelta,?_⟩
      intro x hx
      have hclose : CloseParams x x0 delta := by
        intro i j
        have hi := (dist_pi_lt_iff hdelta).mp hx i
        have hij := (dist_pi_lt_iff hdelta).mp hi j
        simpa only [Real.dist_eq] using hij
      rw [hzero x hclose,hdeg0]
  have hall : ∀ᶠ x in nhds x0, ∀ s : A,
      simplexDegree (EngineMap x) s.val=simplexDegree (EngineMap x0) s.val :=
    Filter.eventually_all.mpr heach
  obtain ⟨delta,hdelta,hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨delta,hdelta,?_⟩
  intro x hx s hs
  have hd : dist x x0 < delta := by
    apply (dist_pi_lt_iff hdelta).mpr
    intro i
    apply (dist_pi_lt_iff hdelta).mpr
    intro j
    simpa only [Real.dist_eq] using hx i j
  exact hball hd ⟨s,hs⟩
end Reuse5
