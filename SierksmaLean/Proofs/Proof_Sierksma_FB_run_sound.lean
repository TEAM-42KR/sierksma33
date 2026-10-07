import SierksmaLean.Definitions.Def_Sierksma_FBRun
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
open Sierksma.FB
open scoped BigOperators

private theorem Sierksma.FB.tab_pe :
    (∀ p < 1855, ∀ f < 37, Sierksma.FB.field (Sierksma.FB.peOf p) f =
      if Nat.testBit (Sierksma.FB.intt f) p then 1 else 0) ∧
    (∀ p < 1855, 9 ≤ ((List.range 36).filter (fun f => Nat.testBit (Sierksma.FB.intt f) p)).length) ∧
    (∀ p < 1855, Nat.testBit (Sierksma.FB.intt 36) p = !Nat.testBit (Sierksma.FB.intt 35) p) ∧
    (∀ f < 37, ∀ p, 1855 ≤ p → Nat.testBit (Sierksma.FB.intt f) p = false) := by
  have hlt : ∀ f < 37, Sierksma.FB.intt f < 2 ^ 1855 := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro f hf p hp
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hlt f hf) (Nat.pow_le_pow_right (by norm_num) hp))

theorem Sierksma.FB.memBits_spec (mem : List ℕ) (i : ℕ) :
    Nat.testBit (memBits mem) i = true ↔ i ∈ mem := by
  induction mem with
  | nil => simp [memBits]
  | cons p ps ih =>
    change Nat.testBit (Nat.lor (Nat.shiftLeft 1 p) (memBits ps)) i = true ↔ i ∈ p :: ps
    rw [Nat.lor_eq, Nat.testBit_or]
    simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
      decide_eq_true_eq, Bool.or_eq_true, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

theorem Sierksma.FB.dead_sound (C K b caps g : ℕ)
    (hg : g < 76545) (hC : Nat.land C (covOf g) = 0)
    (hK : b = 0 ∨ Nat.land K (covOf g) = 0) : Good C K b caps := by
  intro S _ hbox hcard _ hcov
  obtain ⟨i, hi, hc⟩ := hcov g hg
  have hzC := congrArg (fun x => Nat.testBit x i) hC
  have hCi : Nat.testBit C i = false := by
    simpa only [Nat.land_eq, Nat.testBit_and, hc, Bool.and_true, Nat.zero_testBit] using hzC
  rcases hK with hb | hk
  · have hpos : 0 < (S.filter (fun j => Nat.testBit C j = false)).card := by
      apply Finset.card_pos.mpr
      exact ⟨i, by simp [hi, hCi]⟩
    omega
  · have hzK := congrArg (fun x => Nat.testBit x i) hk
    have hKi : Nat.testBit K i = false := by
      simpa only [Nat.land_eq, Nat.testBit_and, hc, Bool.and_true, Nat.zero_testBit] using hzK
    rcases hbox i hi with h | h <;> simp_all

theorem Sierksma.FB.signOK_sound (mem : List ℕ) (q1 q2 : ℕ)
    (hi : incr mem = true) (h1 : quadOK q1 = true)
    (h2 : quadOK q2 = true) (hs : signOK mem q1 q2 = true) :
    ¬ signedIdx mem.toFinset := by
  have props : ∀ (ls : List ℕ) (lo : ℕ), incrAux lo ls = true →
      (∀ p ∈ ls, lo ≤ p ∧ p < 1855) ∧ ls.Nodup := by
    intro ls
    induction ls with
    | nil => intro lo _; simp
    | cons p ps ih =>
      intro lo hh
      simp only [incrAux, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hh
      obtain ⟨hbound, hnd⟩ := ih (p+1) hh.2
      constructor
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hh.1
        · obtain ⟨hlo, hlt⟩ := hbound q hq
          exact ⟨by omega, hlt⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, hnd⟩
        intro hp
        have := (hbound p hp).1
        omega
  have hnd : mem.Nodup := (props mem 0 hi).2
  have sum_shift : ∀ (ls : List ℕ) (w : ℕ → ℕ) (mask j : ℕ),
      sumZ w mask (j+1) ls = sumZ w (mask/2) j ls := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons p ps ih =>
      intro w mask j
      have bit : Nat.testBit mask (j+1) = Nat.testBit (mask/2) j := by
        simpa only [Nat.pow_one] using (Nat.testBit_div_two_pow (n := 1) mask j).symm
      simp only [sumZ, zAt, bit]
      rw [show Nat.succ (j+1) = (j+1)+1 by omega, ih]
  have tofin : ∀ (ls : List ℕ), ls.Nodup → ∀ f : ℕ → ZMod 3,
      (ls.map f).sum = ∑ i ∈ ls.toFinset, f i := by
    intro ls
    induction ls with
    | nil => intro _ f; simp
    | cons p ps ih =>
      intro h f
      simp only [List.nodup_cons] at h
      simp [ih h.2, h.1]
  intro hz
  obtain ⟨z, hnon, hsum, hS2⟩ := hz
  have hcases : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
  have signmask : ∀ (ls : List ℕ), (∀ p ∈ ls, z p ≠ 0) →
      ∃ mask < 2^ls.length, ∀ w : ℕ → ℕ,
        ((sumZ w mask 0 ls : ℕ) : ZMod 3) = (ls.map (fun p => z p * (w p : ZMod 3))).sum := by
    intro ls
    induction ls with
    | nil => intro _; exact ⟨0, by simp, by intro w; simp [sumZ]⟩
    | cons p ps ih =>
      intro hn
      have hp : z p ≠ 0 := hn p (by simp)
      obtain ⟨tail, htail, htail_sum⟩ := ih (by intro q hq; exact hn q (by simp [hq]))
      let d : ℕ := if z p = 2 then 1 else 0
      let mask : ℕ := d + 2*tail
      have hd : d ≤ 1 := by simp only [d]; split <;> omega
      have hdiv : mask/2 = tail := by dsimp [mask]; omega
      have hmod : mask%2 = d := by dsimp [mask]; omega
      refine ⟨mask, ?_, ?_⟩
      · simp only [List.length_cons, Nat.pow_succ]
        dsimp [mask]
        omega
      · intro w
        have hza : ((zAt mask 0 : ℕ) : ZMod 3) = z p := by
          rcases hcases (z p) hp with hp1 | hp2
          · have hd0 : d = 0 := by simp [d, hp1]; decide
            simp [zAt, Nat.testBit_eq_decide_div_mod_eq, hmod, hd0, hp1]
          · have hd1 : d = 1 := by simp [d, hp2]
            simp [zAt, Nat.testBit_eq_decide_div_mod_eq, hmod, hd1, hp2]
        rw [sumZ, sum_shift ps w mask 0, hdiv]
        simp only [Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, List.map_cons, List.sum_cons, hza, htail_sum]
  obtain ⟨mask, hmask, heq⟩ := signmask mem (by simpa using hnon)
  have mod_zero : ∀ n : ℕ, (n : ZMod 3) = 0 → n%3 = 0 := by
    intro n hn
    simpa using congrArg ZMod.val hn
  have hzero : sumZ (fun _ => 1) mask 0 mem % 3 = 0 := by
    apply mod_zero
    rw [heq, tofin mem hnd]
    simpa using hsum
  have neq : ∀ a b : ℕ, Nat.beq a b = false → a ≠ b := by
    intro a b hab heq
    subst b
    simp at hab
  have wzero : ∀ q : ℕ, quadOK q = true → sumZ (w2 q) mask 0 mem % 3 = 0 := by
    intro q hq
    have qvlt : qv q < 9 := Nat.mod_lt _ (by decide)
    have qvplt : qv' q < 9 := Nat.mod_lt _ (by decide)
    simp [quadOK] at hq
    have he := hS2 (qu q) (qv q) (qu' q) (qv' q)
      hq.1.1.1.1.1 hq.1.1.1.1.2 qvlt qvplt (neq _ _ hq.1.1.1.2) (neq _ _ hq.1.1.2) (neq _ _ hq.1.2) (neq _ _ hq.2)
    apply mod_zero
    rw [heq, tofin mem hnd]
    simpa only [w2, Nat.mul_eq, Nat.cast_mul, mul_assoc] using he
  have hzero1 := wzero q1 h1
  have hzero2 := wzero q2 h2
  have hall := (List.all_eq_true.mp hs) mask (List.mem_range.mpr hmask)
  change (!(Nat.beq (sumZ (fun _ => 1) mask 0 mem % 3) 0 &&
    Nat.beq (sumZ (w2 q1) mask 0 mem % 3) 0 &&
    Nat.beq (sumZ (w2 q2) mask 0 mem % 3) 0)) = true at hall
  simp [hzero, hzero1, hzero2] at hall

theorem Sierksma.FB.solParse_sound (C K caps n : ℕ) (l r : List ℕ)
    (h : solParse C n l = some r) : Good C K 0 caps := by
  unfold solParse at h
  split at h
  · cases h
  · rename_i mem l1 hr
    split at h
    · cases h
    · rename_i qs l2 hqs
      split at h
      · rename_i q1 q2
        simp only [Bool.cond_eq_ite] at h
        split at h
        · rename_i hp
          simp only [Bool.and_eq_true, Nat.beq_eq] at hp
          intro S hC hbox hcard _ _
          have eqS : S = mem.toFinset := by
            apply Finset.ext
            intro i
            simp only [List.mem_toFinset]
            constructor
            · intro hi
              have hbit : Nat.testBit C i = true := by
                cases hb : Nat.testBit C i
                · have hn : (S.filter (fun j => Nat.testBit C j = false)).Nonempty :=
                    ⟨i, by simp [hi, hb]⟩
                  have := Finset.card_pos.mpr hn
                  omega
                · rfl
              rw [← hp.1.1.1.2] at hbit
              exact (memBits_spec mem i).mp hbit
            · intro hi
              apply hC i
              rw [← hp.1.1.1.2]
              exact (memBits_spec mem i).mpr hi
          rw [eqS]
          exact signOK_sound mem q1 q2 hp.1.1.1.1 hp.1.1.2 hp.1.2 hp.2
        · cases h
      · cases h

theorem Sierksma.FB.witLoopR_excludes (C K fw n : ℕ) (l r : List ℕ) (S : Finset ℕ)
    (hn : 0 < n) (hbox : ∀ i ∈ S, Nat.testBit C i = false → Nat.testBit K i = true)
    (hcov : coversIdx S)
    (hsmall : (S.filter (fun i => Nat.testBit C i = false ∧
      (fw = 0 ∨ Nat.testBit (intt (fw - 1)) i = true))).card ≤ 1)
    (h : witLoopR C K fw n l K = some r) : False := by
  have get : ∀ g : ℕ, g < 76545 → Nat.land C (covOf g) = 0 →
      (fw = 0 ∨ Nat.land (Nat.land K (covOf g)) (intt (fw-1)) = Nat.land K (covOf g)) →
      ∃ i ∈ S, Nat.testBit C i = false ∧ Nat.testBit K i = true ∧
        Nat.testBit (covOf g) i = true ∧ (fw = 0 ∨ Nat.testBit (intt (fw-1)) i = true) := by
    intro g hg hc hf
    obtain ⟨i, hi, hci⟩ := hcov g hg
    have hz := congrArg (fun x => Nat.testBit x i) hc
    have hC : Nat.testBit C i = false := by
      simpa only [Nat.land_eq, Nat.testBit_and, hci, Bool.and_true, Nat.zero_testBit] using hz
    have hK := hbox i hi hC
    refine ⟨i, hi, hC, hK, hci, ?_⟩
    rcases hf with hf | hf
    · exact Or.inl hf
    · apply Or.inr
      have hb := congrArg (fun x => Nat.testBit x i) hf
      simpa only [Nat.land_eq, Nat.testBit_and, hK, hci, Bool.true_and] using hb
  have step_eq : ∀ (nn : ℕ) (ll : List ℕ) (acc : ℕ),
      witLoopR C K fw (nn+1) ll acc =
        match fetch ll with
        | none => none
        | some (t, l1) =>
          cond (Nat.blt (Nat.shiftRight t 3) 76545 &&
            Nat.beq (Nat.land C (covOf (Nat.shiftRight t 3))) 0 &&
            (Nat.beq fw 0 || Nat.beq
              (Nat.land (Nat.land K (covOf (Nat.shiftRight t 3))) (intt (fw-1)))
              (Nat.land K (covOf (Nat.shiftRight t 3)))))
            (witLoopR C K fw nn l1 (Nat.land acc (covOf (Nat.shiftRight t 3)))) none := by
    intros; rfl
  have track : ∀ (nn : ℕ) (ll : List ℕ) (acc i : ℕ),
      Nat.testBit acc i = true →
      (∀ j ∈ S, Nat.testBit C j = false →
        (fw = 0 ∨ Nat.testBit (intt (fw-1)) j = true) → j = i) →
      witLoopR C K fw nn ll acc = some r → False := by
    intro nn
    induction nn with
    | zero =>
      intro ll acc i hbit _ hw
      have hne : acc ≠ 0 := by intro he; simp [he] at hbit
      simpa [witLoopR, Bool.cond_eq_ite, hne] using hw
    | succ nn ih =>
      intro ll acc i hbit huniq hw
      rw [step_eq] at hw
      split at hw
      · cases hw
      · rename_i t l1 hfetch
        simp only [Bool.cond_eq_ite] at hw
        split at hw
        · rename_i hp
          simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.sub_eq] at hp
          obtain ⟨j, hj, hCj, _, hcvj, hfj⟩ := get (Nat.shiftRight t 3) hp.1.1 hp.1.2 hp.2
          have hji := huniq j hj hCj hfj
          subst j
          apply ih l1 (Nat.land acc (covOf (Nat.shiftRight t 3))) i
          · rw [Nat.land_eq, Nat.testBit_and, hbit, hcvj]
            rfl
          · exact huniq
          · exact hw
        · cases hw
  cases n with
  | zero => omega
  | succ nn =>
    rw [step_eq] at h
    split at h
    · cases h
    · rename_i t l1 hfetch
      simp only [Bool.cond_eq_ite] at h
      split at h
      · rename_i hp
        simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.sub_eq] at hp
        obtain ⟨i, hi, hCi, hKi, hcvi, hfi⟩ := get (Nat.shiftRight t 3) hp.1.1 hp.1.2 hp.2
        apply track nn l1 (Nat.land K (covOf (Nat.shiftRight t 3))) i
        · rw [Nat.land_eq, Nat.testBit_and, hKi, hcvi]
          rfl
        · intro j hj hCj hfj
          exact Finset.card_le_one.mp hsmall j
            (by simp [hj, hCj, hfj]) i (by simp [hi, hCi, hfi])
        · exact h
      · cases h

theorem Sierksma.FB.memMult_field (mem : List ℕ) (f : ℕ)
    (hnd : mem.Nodup) (hlt : ∀ p ∈ mem, p < 1855)
    (hlen : mem.length ≤ 15) (hf : f < 37) :
    field (memMult mem) f = mult mem.toFinset f := by
  have fn : ∀ x k : ℕ, field x k = x / 16^k % 16 := by
    intro x k
    simp only [field, Nat.land_eq, Nat.shiftRight_eq', Nat.mul_eq, Nat.shiftRight_eq_div_pow]
    change (x / 2^(4*k) &&& (2^4-1)) = x / 16^k % 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have hp : 2^(4*k) = 16^k := by rw [pow_mul]; rfl
    rw [hp]
  have dig : ∀ p k : ℕ, p < 1855 → k < 37 →
      peOf p / 16^k % 16 = if Nat.testBit (intt k) p then 1 else 0 := by
    intro p k hp hk
    rw [← fn]
    exact tab_pe.1 p hp k hk
  let R : ℕ → ℕ := Nat.rec 0 (fun k r => r + 16^k)
  have R0 : R 0 = 0 := rfl
  have Rs : ∀ k, R (k+1) = R k + 16^k := by intros; rfl
  have Rid : ∀ k, 15*R k+1 = 16^k := by
    intro k
    induction k with
    | zero => simp [R0]
    | succ k ih => rw [Rs, Nat.pow_succ]; nlinarith
  have low : ∀ k : ℕ, k ≤ 37 → ∀ p < 1855, peOf p % 16^k ≤ R k := by
    intro k
    induction k with
    | zero => intro _ p _; simp only [Nat.pow_zero, Nat.mod_one, R0, le_refl]
    | succ k ih =>
      intro hk p hp
      rw [Nat.pow_succ, Nat.mod_mul]
      have hb := dig p k hp (by omega)
      have hdb : peOf p / 16^k % 16 ≤ 1 := by rw [hb]; split <;> omega
      rw [Rs]
      have hl := ih (by omega) p hp
      exact Nat.add_le_add hl (by simpa using Nat.mul_le_mul_left (16^k) hdb)
  have lowsum : ∀ (ls : List ℕ), (∀ p ∈ ls, p < 1855) → ∀ k ≤ 37,
      (ls.map (fun p => peOf p % 16^k)).sum ≤ ls.length * R k := by
    intro ls
    induction ls with
    | nil => intros; simp
    | cons p ps ih =>
      intro hb k hk
      have hl := low k hk p (hb p (by simp))
      have ht := ih (by intro q hq; exact hb q (by simp [hq])) k hk
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have modsum : ∀ (ls : List ℕ) (w : ℕ → ℕ) (m : ℕ),
      (ls.map w).sum % m = (ls.map (fun p => w p % m)).sum % m := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons p ps ih =>
      intro w m
      simp only [List.map_cons, List.sum_cons]
      simp only [Nat.add_mod, Nat.mod_mod, ih]
  have small : ∀ k ≤ 37, (mem.map (fun p => peOf p % 16^k)).sum < 16^k := by
    intro k hk
    have hb := lowsum mem hlt k hk
    have hr := Rid k
    have hm : mem.length * R k ≤ 15*R k := Nat.mul_le_mul_right (R k) hlen
    omega
  have MM : ∀ ls : List ℕ, memMult ls = (ls.map peOf).sum := by
    intro ls
    induction ls with
    | nil => rfl
    | cons p ps ih =>
      change Nat.add (peOf p) (memMult ps) = peOf p + (ps.map peOf).sum
      rw [Nat.add_eq, ih]
  have sumsplit : ∀ ls : List ℕ, (ls.map (fun p => peOf p % 16^(f+1))).sum =
      (ls.map (fun p => peOf p % 16^f)).sum +
        16^f * (ls.map (fun p => peOf p / 16^f % 16)).sum := by
    intro ls
    induction ls with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Nat.pow_succ, Nat.mod_mul] at *
      rw [ih]
      ring
  have sumdigit : (mem.map (fun p => peOf p / 16^f % 16)).sum = mult mem.toFinset f := by
    have tofin : ∀ ls : List ℕ, ls.Nodup → ∀ w : ℕ → ℕ,
        (ls.map w).sum = ∑ p ∈ ls.toFinset, w p := by
      intro ls
      induction ls with
      | nil => intros; simp
      | cons p ps ih =>
        intro hn w
        simp only [List.nodup_cons] at hn
        simp [ih hn.2, hn.1]
    rw [tofin mem hnd]
    have hd : ∀ p ∈ mem.toFinset, peOf p / 16^f % 16 = if Nat.testBit (intt f) p then 1 else 0 := by
      intro p hp
      exact dig p f (hlt p (by simpa using hp)) hf
    rw [Finset.sum_congr rfl hd]
    simp [mult]
  rw [fn, MM mem, ← Nat.mod_mul_right_div_self, ← Nat.pow_succ]
  rw [modsum, Nat.mod_eq_of_lt (small (f+1) (by omega)), sumsplit mem]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (small f (by omega))]
  simpa using sumdigit

theorem Sierksma.FB.testBit_sub (A B : ℕ)
    (h : ∀ i, Nat.testBit B i = true → Nat.testBit A i = true) (i : ℕ) :
    Nat.testBit (A-B) i = (Nat.testBit A i && !(Nat.testBit B i)) := by
  have sh : ∀ x j : ℕ, Nat.testBit (x/2) j = Nat.testBit x (j+1) := by
    intro x j
    simpa only [Nat.pow_one] using Nat.testBit_div_two_pow (n := 1) x j
  induction i generalizing A B with
  | zero =>
    have hle : B ≤ A := Nat.le_of_testBit h
    have hlow : B%2 = 1 → A%2 = 1 := by
      intro hb
      have hb' : Nat.testBit B 0 = true := by
        simp [Nat.testBit_eq_decide_div_mod_eq, hb]
      have ha' := h 0 hb'
      simpa [Nat.testBit_eq_decide_div_mod_eq] using ha'
    rcases Nat.mod_two_eq_zero_or_one A with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one B with hb | hb
    · have hd : (A-B)%2 = 0 := by omega
      simp [Nat.testBit_eq_decide_div_mod_eq, ha, hb, hd]
    · have := hlow hb
      omega
    · have hd : (A-B)%2 = 1 := by omega
      simp [Nat.testBit_eq_decide_div_mod_eq, ha, hb, hd]
    · have hd : (A-B)%2 = 0 := by omega
      simp [Nat.testBit_eq_decide_div_mod_eq, ha, hb, hd]
  | succ i ih =>
    have hle : B ≤ A := Nat.le_of_testBit h
    have hlow : B%2 ≤ A%2 := by
      have hh := h 0
      simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one,
        decide_eq_true_eq] at hh
      omega
    have hd : (A-B)/2 = A/2-B/2 := by omega
    have hh : ∀ j, Nat.testBit (B/2) j = true → Nat.testBit (A/2) j = true := by
      intro j hj
      rw [sh] at hj ⊢
      exact h (j+1) hj
    rw [← sh, hd, ih _ _ hh, sh, sh]

theorem Sierksma.FB.chkR_excludes (fuel caps : ℕ) (ext : List (ℕ × ℕ × ℕ))
    (hext : ∀ e ∈ ext, Good e.1 e.2.1 e.2.2 caps)
    (S : Finset ℕ) (hs : signedIdx S) (hc : capOK S caps) (hcov : coversIdx S) :
    ∀ (mem : List ℕ) (K b : ℕ), mem.Nodup → (∀ p ∈ mem, p < 1855) → mem.length + b ≤ 15 →
      (∀ p ∈ mem, p ∈ S) → (∀ i ∈ S, i ∈ mem ∨ Nat.testBit K i = true) →
      (S.filter (fun i => i ∉ mem)).card ≤ b → (∀ p ∈ mem, Nat.testBit K p = false) →
      (∀ i, Nat.testBit K i = true → i < 1855) →
      (∀ l r : List ℕ, chkR caps ext fuel 0 l (memBits mem) K b (memMult mem) 0 = some r → False) ∧
      (∀ A : ℕ, (∀ i, Nat.testBit A i = true → Nat.testBit K i = true) → 0 < b →
        (∃ i ∈ S, Nat.testBit A i = true) → ∀ l r : List ℕ,
          chkR caps ext fuel 1 l (memBits mem) K b (memMult mem) A = some r → False) := by
  classical
  have bf : ∀ mem : List ℕ, ∀ i, Nat.testBit (memBits mem) i = false ↔ i ∉ mem := by
    intro mem i
    cases hb : Nat.testBit (memBits mem) i
    · have hn : i ∉ mem := by intro hi; have ht := (memBits_spec mem i).mpr hi; simp_all
      simp [hb, hn]
    · have hi := (memBits_spec mem i).mp hb
      simp [hb, hi]
  have nth_mem : ∀ (xs : List (ℕ × ℕ × ℕ)) (n : ℕ) e, nth? xs n = some e → e ∈ xs := by
    intro xs
    induction xs with
    | nil => intros; contradiction
    | cons x xs ih =>
      intro n e hn
      cases n with
      | zero => simp only [nth?, Option.some.injEq] at hn; subst e; simp
      | succ n => exact List.mem_cons_of_mem x (ih n e hn)
  have step_eq : ∀ fuel mode l C K b M A, chkR caps ext (fuel+1) mode l C K b M A =
      stepR caps ext (chkR caps ext fuel) mode l C K b M A := by intros; rfl
  induction fuel with
  | zero =>
    intro mem K b hd hl hb hin hout hcard hdis hKb
    constructor
    · intro l r h; cases h
    · intro A ha hb haS l r h; cases h
  | succ fuel ih =>
    intro mem K b hd hl hb hin hout hcard hdis hKb
    have field_card : ∀ f : ℕ, mult mem.toFinset f +
        (S.filter (fun i => i ∉ mem ∧ Nat.testBit (intt f) i = true)).card = mult S f := by
      intro f
      have e1 : (S.filter (fun i => Nat.testBit (intt f) i = true)).filter (fun i => i ∈ mem) =
          mem.toFinset.filter (fun i => Nat.testBit (intt f) i = true) := by
        ext i
        simp only [Finset.mem_filter, List.mem_toFinset]
        constructor
        · rintro ⟨⟨_, hit⟩, him⟩; exact ⟨him, hit⟩
        · rintro ⟨him, hit⟩; exact ⟨⟨hin i him, hit⟩, him⟩
      have e2 : (S.filter (fun i => Nat.testBit (intt f) i = true)).filter (fun i => i ∉ mem) =
          S.filter (fun i => i ∉ mem ∧ Nat.testBit (intt f) i = true) := by
        ext i; simp only [Finset.mem_filter]; tauto
      have hh := Finset.card_filter_add_card_filter_not
        (s := S.filter (fun i => Nat.testBit (intt f) i = true)) (fun i => i ∈ mem)
      rw [e1, e2] at hh
      exact hh
    have badGood : Good (memBits mem) K b caps → False := by
      intro hg
      apply hg S ?_ ?_ ?_ hc hcov hs
      · intro i hi; exact hin i ((memBits_spec mem i).mp hi)
      · intro i hi; rcases hout i hi with hm | hk
        · exact Or.inl ((memBits_spec mem i).mpr hm)
        · exact Or.inr hk
      · simpa only [bf] using hcard
    constructor
    · intro l r h
      rw [step_eq] at h
      unfold stepR at h
      split at h
      · cases h
      · rename_i t l1 hfetch
        simp only [Bool.cond_eq_ite, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq,
          Bool.and_eq_true, Bool.or_eq_true, if_pos rfl, ite_true, ite_false] at h
        by_cases hop0 : Nat.land t 7 = 0
        · rw [if_pos hop0] at h
          cases he : nth? ext (Nat.sub (Nat.shiftRight t 3) 1) with
          | none => rw [he] at h; cases h
          | some e =>
            rcases e with ⟨C',K',b'⟩
            simp only [he] at h
            split at h
            · rename_i hp
              rcases hp with ⟨⟨⟨_, hC⟩, hK⟩, hb'⟩
              have hg := hext (C',K',b') (nth_mem ext _ _ he)
              rw [hC,hK,hb'] at hg
              exact badGood hg
            · cases h
        · rw [if_neg hop0] at h
          by_cases hop1 : Nat.land t 7 = 1
          · rw [if_pos hop1] at h
            split at h
            · rename_i hp
              exact badGood (dead_sound _ _ _ _ _ hp.1.1 hp.1.2 hp.2)
            · cases h
          · rw [if_neg hop1] at h
            by_cases hop2 : Nat.land t 7 = 2
            · rw [if_pos hop2] at h
              by_cases hfw : Nat.div (Nat.shiftRight t 3) 64 = 0
              · rw [if_pos hfw] at h
                simp only [Nat.ble_eq] at h
                split at h
                · rename_i hp
                  apply witLoopR_excludes (memBits mem) K _ _ l1 r S (by omega) ?_ hcov ?_ h
                  · intro i hi hCi
                    rcases hout i hi with hm | hk
                    · exact False.elim ((bf mem i).mp hCi hm)
                    · exact hk
                  · simpa only [bf, hfw, true_or, and_true] using le_trans hcard hp.2
                · cases h
              · rw [if_neg hfw] at h
                simp only [Bool.and_eq_true, Nat.ble_eq, Nat.sub_eq, Nat.add_eq] at h
                split at h
                · rename_i hp
                  have hf : Nat.div (Nat.shiftRight t 3) 64 - 1 < 37 := by omega
                  have hm := memMult_field mem _ hd hl (by omega) hf
                  have hh := field_card (Nat.div (Nat.shiftRight t 3) 64 - 1)
                  have hcap := hc _ hf
                  rw [hm] at hp
                  have hsmall : (S.filter (fun i => i ∉ mem ∧
                      Nat.testBit (intt (Nat.div (Nat.shiftRight t 3) 64 - 1)) i = true)).card ≤ 1 := by omega
                  apply witLoopR_excludes (memBits mem) K _ _ l1 r S (by omega) ?_ hcov ?_ h
                  · intro i hi hCi
                    rcases hout i hi with hm | hk
                    · exact False.elim ((bf mem i).mp hCi hm)
                    · exact hk
                  · simpa only [bf, hfw, false_or] using hsmall
                · cases h
            · rw [if_neg hop2] at h
              by_cases hop3 : Nat.land t 7 = 3
              · rw [if_pos hop3] at h
                split at h
                · rename_i hp
                  have hm := memMult_field mem (Nat.shiftRight t 3) hd hl (by omega) hp.1
                  have hh := field_card (Nat.shiftRight t 3)
                  have hcap := hc _ hp.1
                  rw [hm] at hp
                  have hzero : (S.filter (fun i => i ∉ mem ∧ Nat.testBit (intt (Nat.shiftRight t 3)) i = true)).card = 0 := by omega
                  have htf : ∀ i ∈ S, i ∉ mem → Nat.testBit (intt (Nat.shiftRight t 3)) i = false := by
                    intro i hi him
                    cases ht : Nat.testBit (intt (Nat.shiftRight t 3)) i
                    · rfl
                    · have hpos : 0 < (S.filter (fun i => i ∉ mem ∧ Nat.testBit (intt (Nat.shiftRight t 3)) i = true)).card :=
                        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi,him,ht⟩⟩
                      omega
                  have hsub : ∀ i, Nat.testBit (Nat.land K (intt (Nat.shiftRight t 3))) i = true → Nat.testBit K i = true := by
                    intro i hi
                    rw [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at hi
                    exact hi.1
                  have hbits := testBit_sub K (Nat.land K (intt (Nat.shiftRight t 3))) hsub
                  have hnewout : ∀ i ∈ S, i ∈ mem ∨ Nat.testBit (K-Nat.land K (intt (Nat.shiftRight t 3))) i = true := by
                    intro i hi
                    by_cases him : i ∈ mem
                    · exact Or.inl him
                    · have hKi : Nat.testBit K i = true := (hout i hi).resolve_left him
                      apply Or.inr
                      rw [hbits, Nat.land_eq, Nat.testBit_and, hKi, htf i hi him]
                      rfl
                  have hnewdis : ∀ i ∈ mem, Nat.testBit (K-Nat.land K (intt (Nat.shiftRight t 3))) i = false := by
                    intro i hi
                    rw [hbits, hdis i hi]
                    rfl
                  have hnewbound : ∀ i, Nat.testBit (K-Nat.land K (intt (Nat.shiftRight t 3))) i = true → i < 1855 := by
                    intro i hi
                    rw [hbits, Bool.and_eq_true] at hi
                    exact hKb i hi.1
                  exact (ih mem _ b hd hl hb hin hnewout hcard hnewdis hnewbound).1 l1 r h
                · cases h
              · rw [if_neg hop3] at h
                by_cases hop4 : Nat.land t 7 = 4
                · rw [if_pos hop4] at h
                  split at h
                  · rename_i hp
                    obtain ⟨i, hi, hci⟩ := hcov _ hp.1.1
                    have hz := congrArg (fun x => Nat.testBit x i) hp.1.2
                    have hCi : Nat.testBit (memBits mem) i = false := by
                      simpa only [Nat.land_eq, Nat.testBit_and, hci, Bool.and_true, Nat.zero_testBit] using hz
                    have him := (bf mem i).mp hCi
                    have hKi := (hout i hi).resolve_left him
                    apply (ih mem K b hd hl hb hin hout hcard hdis hKb).2
                      (Nat.land K (covOf (Nat.shiftRight t 3))) ?_ (by omega) ?_ l1 r h
                    · intro j hj
                      rw [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at hj
                      exact hj.1
                    · refine ⟨i,hi,?_⟩
                      rw [Nat.land_eq, Nat.testBit_and, hKi,hci]
                      rfl
                  · cases h
                · rw [if_neg hop4] at h
                  by_cases hop7 : Nat.land t 7 = 7
                  · rw [if_pos hop7] at h
                    split at h
                    · rename_i hp
                      apply badGood
                      rw [hp]
                      exact solParse_sound _ _ _ _ _ _ h
                    · cases h
                  · rw [if_neg hop7] at h; cases h
    · intro A ha hbpos haS l r h
      rw [step_eq] at h
      unfold stepR at h
      split at h
      · cases h
      · rename_i t l1 hfetch
        simp only [Bool.cond_eq_ite, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq,
          Bool.and_eq_true, Bool.or_eq_true, if_neg (by decide : (1 : ℕ) ≠ 0), ite_true, ite_false] at h
        by_cases hop5 : Nat.land t 7 = 5
        · rw [if_pos hop5] at h
          split at h
          · rename_i hA
            obtain ⟨i, hi, hAi⟩ := haS
            simp [hA] at hAi
          · cases h
        · rw [if_neg hop5] at h
          by_cases hop6 : Nat.land t 7 = 6
          · rw [if_pos hop6] at h
            by_cases hA : Nat.land A (Nat.shiftLeft 1 (Nat.shiftRight t 3)) = 0
            · rw [if_pos hA] at h; cases h
            · rw [if_neg hA] at h
              split at h
              · cases h
              · rename_i l2 hchild
                let g := Nat.shiftRight t 3
                let lb := Nat.shiftLeft 1 g
                have single : ∀ i, Nat.testBit lb i = decide (i = g) := by
                  intro i
                  simp only [lb, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
                  by_cases hi : i = g
                  · subst i; rfl
                  · have hi' : g ≠ i := Ne.symm hi
                    simp [hi,hi']
                have hAg : Nat.testBit A g = true := by
                  cases hag : Nat.testBit A g
                  · apply False.elim
                    apply hA
                    apply Nat.eq_of_testBit_eq
                    intro i
                    rw [Nat.land_eq, Nat.testBit_and, single, Nat.zero_testBit]
                    by_cases hi : i = g
                    · subst i; simp [hag]
                    · simp [hi]
                  · rfl
                have hKg := ha g hAg
                have hgb := hKb g hKg
                have hLbA : ∀ i, Nat.testBit lb i = true → Nat.testBit A i = true := by
                  intro i hi
                  rw [single, decide_eq_true_eq] at hi
                  subst i
                  exact hAg
                have hLbK : ∀ i, Nat.testBit lb i = true → Nat.testBit K i = true := by
                  intro i hi
                  exact ha i (hLbA i hi)
                have kbits : ∀ i, Nat.testBit (K-lb) i = (Nat.testBit K i && !decide (i=g)) := by
                  intro i; rw [testBit_sub K lb hLbK i, single]
                have abits : ∀ i, Nat.testBit (A-lb) i = (Nat.testBit A i && !decide (i=g)) := by
                  intro i; rw [testBit_sub A lb hLbA i, single]
                have knewbound : ∀ i, Nat.testBit (K-lb) i = true → i < 1855 := by
                  intro i hi
                  rw [kbits, Bool.and_eq_true] at hi
                  exact hKb i hi.1
                have knewdis : ∀ i ∈ mem, Nat.testBit (K-lb) i = false := by
                  intro i hi; rw [kbits,hdis i hi]; rfl
                have bitnew : ∀ i, i ≠ g → Nat.testBit K i = true → Nat.testBit (K-lb) i = true := by
                  intro i hi hKi
                  rw [kbits,hKi]
                  simp [hi]
                by_cases hgS : g ∈ S
                · have hgm : g ∉ mem := by
                    intro hgm
                    have := hdis g hgm
                    simp_all
                  have hd' : (g::mem).Nodup := List.nodup_cons.mpr ⟨hgm,hd⟩
                  have hl' : ∀ i ∈ g::mem, i < 1855 := by
                    intro i hi
                    rcases List.mem_cons.mp hi with rfl | hi
                    · exact hgb
                    · exact hl i hi
                  have hb' : (g::mem).length + (b-1) ≤ 15 := by simp only [List.length_cons]; omega
                  have hin' : ∀ i ∈ g::mem, i ∈ S := by
                    intro i hi
                    rcases List.mem_cons.mp hi with rfl | hi
                    · exact hgS
                    · exact hin i hi
                  have hout' : ∀ i ∈ S, i ∈ g::mem ∨ Nat.testBit (K-lb) i = true := by
                    intro i hi
                    rcases hout i hi with him | hKi
                    · exact Or.inl (List.mem_cons_of_mem g him)
                    · by_cases hig : i = g
                      · subst i; exact Or.inl (by simp)
                      · exact Or.inr (bitnew i hig hKi)
                  have he : S.filter (fun i => i ∉ g::mem) = (S.filter (fun i => i ∉ mem)).erase g := by
                    ext i
                    simp only [Finset.mem_filter, Finset.mem_erase, List.mem_cons, not_or]
                    tauto
                  have hcard' : (S.filter (fun i => i ∉ g::mem)).card ≤ b-1 := by
                    rw [he, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hgS,hgm⟩)]
                    exact Nat.sub_le_sub_right hcard 1
                  have hdis' : ∀ i ∈ g::mem, Nat.testBit (K-lb) i = false := by
                    intro i hi
                    rcases List.mem_cons.mp hi with rfl | hi
                    · rw [kbits]; simp
                    · exact knewdis i hi
                  have eC : Nat.lor (memBits mem) lb = memBits (g::mem) := by
                    change Nat.lor (memBits mem) lb = Nat.lor lb (memBits mem)
                    rw [Nat.lor_eq,Nat.lor_eq]
                    exact Nat.or_comm _ _
                  have eM : Nat.add (memMult mem) (peOf g) = memMult (g::mem) := by
                    change Nat.add (memMult mem) (peOf g) = Nat.add (peOf g) (memMult mem)
                    simp only [Nat.add_eq,Nat.add_comm]
                  change chkR caps ext fuel 0 l1 (Nat.lor (memBits mem) lb) (K-lb) (b-1)
                    (Nat.add (memMult mem) (peOf g)) 0 = some l2 at hchild
                  rw [eC,eM] at hchild
                  exact (ih (g::mem) (K-lb) (b-1) hd' hl' hb' hin' hout' hcard' hdis' knewbound).1 l1 l2 hchild
                · have hout' : ∀ i ∈ S, i ∈ mem ∨ Nat.testBit (K-lb) i = true := by
                    intro i hi
                    rcases hout i hi with hm | hKi
                    · exact Or.inl hm
                    · have hig : i ≠ g := by intro he; subst i; exact hgS hi
                      exact Or.inr (bitnew i hig hKi)
                  have hanew : ∀ i, Nat.testBit (A-lb) i = true → Nat.testBit (K-lb) i = true := by
                    intro i hi
                    rw [abits, Bool.and_eq_true] at hi
                    have hig : i ≠ g := by
                      intro he
                      subst i
                      simp at hi
                    exact bitnew i hig (ha i hi.1)
                  have haS' : ∃ i ∈ S, Nat.testBit (A-lb) i = true := by
                    obtain ⟨i, hi, hAi⟩ := haS
                    have hig : i ≠ g := by intro he; subst i; exact hgS hi
                    refine ⟨i,hi,?_⟩
                    rw [abits,hAi]
                    simp [hig]
                  exact (ih mem (K-lb) b hd hl hb hin hout' hcard knewdis knewbound).2
                    (A-lb) hanew hbpos haS' l2 r h

          · rw [if_neg hop6] at h; cases h

theorem proof_Sierksma_FB_run_sound (s mem : List ℕ) (K b caps : ℕ) (ext : List (ℕ × ℕ × ℕ))
    (h : runR s mem K b caps ext = true)
    (hext : ∀ e ∈ ext, Good e.1 e.2.1 e.2.2 caps) :
    Good (memBits mem) K b caps := by
  have props : ∀ (ls : List ℕ) (lo : ℕ), incrAux lo ls = true →
      (∀ p ∈ ls, lo ≤ p ∧ p < 1855) ∧ ls.Nodup := by
    intro ls
    induction ls with
    | nil => intro lo _; simp
    | cons p ps ih =>
      intro lo hh
      simp only [incrAux, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hh
      obtain ⟨hbound, hnd⟩ := ih (p+1) hh.2
      constructor
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hh.1
        · obtain ⟨hlo, hlt⟩ := hbound q hq
          exact ⟨by omega, hlt⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, hnd⟩
        intro hp
        have := (hbound p hp).1
        omega
  have bf : ∀ i, Nat.testBit (memBits mem) i = false ↔ i ∉ mem := by
    intro i
    cases hb : Nat.testBit (memBits mem) i
    · have hn : i ∉ mem := by intro hi; have ht := (memBits_spec mem i).mpr hi; simp_all
      simp [hb, hn]
    · have hi := (memBits_spec mem i).mp hb
      simp [hb, hi]
  unfold runR at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, Nat.add_eq] at h
  rcases h with ⟨⟨⟨⟨hincr, hlen⟩, hdis⟩, hK⟩, hchk⟩
  obtain ⟨hbound,hnd⟩ := props mem 0 hincr
  have hl : ∀ p ∈ mem, p < 1855 := by intro p hp; exact (hbound p hp).2
  have hdis' : ∀ p ∈ mem, Nat.testBit K p = false := by
    intro p hp
    have hb := congrArg (fun x => Nat.testBit x p) hdis
    have hC := (memBits_spec mem p).mpr hp
    simpa only [Nat.land_eq, Nat.testBit_and, hC, Bool.true_and, Nat.zero_testBit] using hb
  have hltK : K < 2^1855 := by
    apply lt_of_le_of_lt hK
    change 2^1855-1 < 2^1855
    exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hKb : ∀ i, Nat.testBit K i = true → i < 1855 := by
    intro i hi
    by_contra hn
    have hn' : 1855 ≤ i := by omega
    have hpow : 2^1855 ≤ 2^i := Nat.pow_le_pow_right (by decide) hn'
    have hb := Nat.ge_two_pow_of_testBit hi
    omega
  have finish : ∀ fuel : ℕ,
      (match chkR caps ext fuel 0 s (memBits mem) K b (memMult mem) 0 with
        | none => false | some _ => true) = true → Good (memBits mem) K b caps := by
    intro fuel hchk'
    cases hr : chkR caps ext fuel 0 s (memBits mem) K b (memMult mem) 0 with
    | none => simp only [hr, Bool.false_eq_true] at hchk'
    | some r =>
      intro S hchosen hbox hcard hc hcov hs
      have hin : ∀ p ∈ mem, p ∈ S := by
        intro p hp
        exact hchosen p ((memBits_spec mem p).mpr hp)
      have hout : ∀ i ∈ S, i ∈ mem ∨ Nat.testBit K i = true := by
        intro i hi
        rcases hbox i hi with hC | hK
        · exact Or.inl ((memBits_spec mem i).mp hC)
        · exact Or.inr hK
      have hcard' : (S.filter (fun i => i ∉ mem)).card ≤ b := by
        simpa only [bf] using hcard
      exact (chkR_excludes fuel caps ext hext S hs hc hcov mem K b
        hnd hl hlen hin hout hcard' hdis' hKb).1 s r hr
  exact finish 4000000 hchk
