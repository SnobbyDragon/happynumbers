import tactic
import data.nat.digits
import logic.basic
import data.list

namespace happynumber

-- no longer using B and ℕ+
/-
def B := set.Ioi (1 : ℕ)
#check B
#reduce 5 ∈ B

#reduce nat.has_pow
def pow (n : ℕ) (p : ℕ+) : ℕ := nat.pow n p
instance : has_pow ℕ ℕ+ := ⟨pow⟩
-/


section definitions

-- Perfect digital invariant (a.k.a. happy function)
-- the sum of the pth (p > 0) power of digits of a natural number n in a base b > 1
def happyfunction (p : ℕ) (b : ℕ) : ℕ → ℕ
| n := ((digits b n).map (λ d, d^p)).sum

-- gets the ith iteration of the happy function w/base b, power p on natural number n
def happyfunction' (p : ℕ) (b : ℕ) (n : ℕ) : ℕ → ℕ
| 0 := n
| (i+1) := happyfunction p b (happyfunction' (i))

-- Happy number
-- a number n is b-happy iff the happy function on n w/base b, power 2 eventually equals 1
def happy (b : ℕ) (n : ℕ) : Prop := ∃ (j : ℕ), happyfunction' 2 b n j = 1

-- height of a b-happy number n is the number of iterations of the happy function to reach 1
def happyheight (b : ℕ) (n : ℕ) (H : happy b n) : ℕ := sorry

--Sad number
-- a number n is b-sad iff all iterations of the happy function on n w/base b, power 2 are not equal to 1
def sad (b : ℕ) (n : ℕ): Prop := ∀ (j : ℕ), happyfunction' 2 b n j ≠ 1

end definitions

-- one iteration of happy function
@[simp]
lemma happyfunction'_one_eq_happyfunction (p b n : ℕ) : happyfunction' p b n 1 = happyfunction p b n :=
begin
  unfold happyfunction',
end

-- commutative composition but not really bc it's technically the same function
lemma happyfunction'_comm (p b n i : ℕ) : happyfunction p b (happyfunction' p b n i) = happyfunction' p b (happyfunction p b n) i :=
begin
  rw <- happyfunction',
  induction i with k nk,
  unfold happyfunction',
  unfold happyfunction' at *,
  rw nk,
end

-- happy = not sad
lemma happy_not_sad (b n : ℕ) : happy b n ↔ ¬(sad b n) :=
begin
  split,
  intros H S,
  cases H with k Hk,
  specialize S k,
  contradiction,
  intros S,
  unfold sad at S,
  --rw <- not_exists at S,
  simp at S,
  cases S with k Sk,
  use k,
  exact Sk,
end

-- every natural number n is either happy or sad (but not both)
lemma happy_or_sad (b: ℕ) : ∀ (n : ℕ), happy b n ∨ sad b n :=
begin
  intros n,
  rw happy_not_sad,
  finish,
end

-- happy function on 1 equals 1 for any p > 0 and b > 1
lemma happyfunction_one (p : ℕ) (b : ℕ) : (b > 1) → happyfunction p b 1 = 1 :=
begin
  intros h,
  unfold happyfunction,
  have H : digits b 1 = [1],
  apply digits_of_lt,
  linarith,
  exact h,
  rw H,
  simp,
end

-- junk input. b = 0
lemma junk_zero_one (p : ℕ) : happyfunction p 0 1 = 1 :=
begin
  unfold happyfunction,
  have H : digits 0 1 = [1],
  refl,
  rw H,
  simp,
end

-- junk input. b = 1
lemma junk_one_one (p : ℕ) : happyfunction p 1 1 = 1 :=
begin
  unfold happyfunction,
  have H : digits 1 1 = [1],
  refl,
  rw H,
  simp,
end

-- just to not deal with b > 1 hypothesis
@[simp]
lemma happyfunction_one' (p : ℕ) (b : ℕ) : happyfunction p b 1 = 1 :=
begin
  have H : (b = 0) ∨ (1 = b) ∨ (1 < b),
  cases b,
  left,
  refl,
  right,
  have H := nat.succ_pos b,
  have H' : 1 ≤ b.succ,
  linarith,
  rw le_iff_eq_or_lt at H',
  exact H',
  cases H,
  rw H,
  exact junk_zero_one p,
  cases H,
  rw <- H,
  exact junk_one_one p,
  exact happyfunction_one p b H,
end

-- any iteration of the happy function on 1 equals 1
@[simp]
lemma happyfunction'_one (p : ℕ) (b : ℕ) : ∀ (i : ℕ), happyfunction' p b 1 i = 1 :=
begin
  intros i,
  induction i with k ik,
  unfold happyfunction',
  unfold happyfunction',
  rw ik,
  exact happyfunction_one' p b,
end

-- for base 10, after reaching 1, will stay 1
lemma ten_happily_ever_after (n : ℕ) (j: ℕ) : happyfunction' 2 10 n j = 1 → ∀ (i : ℕ), (j ≤ i) → happyfunction' 2 10 n i = 1 :=
begin
  intros H i hi,
  rw le_iff_exists_add at hi,
  cases hi with c hc,
  induction c with k ck generalizing i,
  { simp at hc,
    rw hc,
    exact H,
  },
  { rw nat.add_succ at hc,
    rw hc,
    unfold happyfunction',
    specialize ck (j+k),
    simp at ck,
    rw ck,
    --unfold happyfunction,
    simp,
  },
end

-- for base b, after reaching 1, will stay 1
lemma happily_ever_after (b : ℕ) (n : ℕ) (j: ℕ) : happyfunction' 2 b n j = 1 → ∀ i, (j ≤ i) → happyfunction' 2 b n i = 1 :=
begin
  intros H i hi,
  rw le_iff_exists_add at hi,
  cases hi with c hc,
  induction c with k ck generalizing i,
   { simp at hc,
     rw hc,
     exact H,
  }, 
  { rw nat.add_succ at hc,
    rw hc,
    unfold happyfunction',
    specialize ck (j+k),
    simp at ck,
    rw ck,
    --exact happyfunction_one' 2 b,
    simp,
  },
end

-- 1 is 10-happy
lemma ten_happy_one : happy 10 1 :=
begin
  use 0,
  unfold happyfunction',
end

-- 7 is 10-happy
lemma ten_happy_seven : happy 10 7 :=
begin
  use 5,
  unfold happyfunction',
  unfold happyfunction,
  norm_num,
end

-- happy function on 0 equals 0
@[simp]
lemma happyfunction_zero  (p : ℕ) (b : ℕ) : happyfunction p b 0 = 0 :=
begin
  unfold happyfunction,
  simp,
end

-- any iteration of the happy function on 0 equals 0
@[simp]
lemma happyfunction'_zero (p : ℕ) (b : ℕ) : ∀ (i : ℕ), happyfunction' p b 0 i = 0 :=
begin
  intros i,
  induction i with k ik,
  unfold happyfunction',
  unfold happyfunction',
  rw ik,
  --unfold happyfunction,
  simp,
end

 -- 0 is 10-sad
lemma ten_sad_zero : sad 10 0 :=
begin
  intros i hi,
  --rw happyfunction'_zero 2 10 i at hi,
  --linarith,
  simp at hi,
  exact hi,
end

-- for b=10, multiplying by 10 (adding a zero) won't make a difference
lemma ten_happyfunction_eq_times_ten (n : ℕ) : happyfunction 2 10 n = happyfunction 2 10 (10*n) :=
begin
  cases n,
  norm_num,
  have H : digits 10 (10*n.succ) = 0 :: digits 10 n.succ,
  have h₁ : 10*n.succ = 0 + 10*n.succ,
  simp,
  rw h₁,
  apply digits_add,
  linarith,
  linarith,
  right,
  exact nat.succ_pos n,
  unfold happyfunction,
  rw H,
  norm_num,
end

lemma ten_happyfunction'_eq_times_ten (n : ℕ) : ∀ (i : ℕ), (0 < i) → happyfunction' 2 10 n i = happyfunction' 2 10 (10*n) i :=
begin
  intros i i_pos,
  cases i,
  exfalso,
  linarith,
  unfold happyfunction',
  rw happyfunction'_comm,
  rw happyfunction'_comm 2 10 (10*n),
  rw ten_happyfunction_eq_times_ten,
end

-- if n is 10-happy, then n*10 is 10-happy
lemma ten_happy_times_ten (n : ℕ) : happy 10 n → happy 10 (10*n) :=
begin
  intros H,
  cases H with j Hj,
  cases j,
  use 1,
  rw happyfunction'_one_eq_happyfunction,
  unfold happyfunction' at Hj,
  rw Hj,
  rw <- ten_happyfunction_eq_times_ten,
  simp,
  use j.succ,
  rw <- ten_happyfunction'_eq_times_ten n j.succ (nat.succ_pos'),
  exact Hj,
end

-- 10^m is always a 10-happy number
lemma ten_happy_pow_ten (m : ℕ) : happy 10 (10^m) :=
begin
  use 1,
  unfold happyfunction',
  induction m with k mk,
  rw nat.pow_zero 10,
  exact happyfunction_one' 2 10,
  rw nat.pow_succ,
  rw mul_comm,
  rw <- ten_happyfunction_eq_times_ten (10^k),
  exact mk,
end

-- for b=10, permuting the digits won't make a difference
lemma happyfunction_eq_permute_digits_ten (p : ℕ) (n n' : ℕ) (P : (digits 10 n) ~ (digits 10 n')) : happyfunction p 10 n = happyfunction p 10 n' :=
begin
  sorry
end

-- permuting a 10-happy number's digits will result in another happy number
lemma ten_happy_permute_ten_happy (b : ℕ) (n : ℕ) (H : happy b n) (n' : ℕ) (P : (digits b n) ~ (digits b n')) : happy b n' :=
begin
  sorry
end


-- references "A Set of Eight Numbers" - Arthur Porges
-- https://oeis.org/A003621/a003621.pdf
section mainTheorem

-- the base 10 digits of a number are all at most 9
-- Thanks Kevin Buzzard for digits_lt_base :)
lemma ten_digits_le_9 (n : ℕ) : ∀ (d ∈ (digits 10 n)), d ≤ 9 :=
begin
  intros d H,
  have H' := digits_lt_base (by linarith) H,
  linarith,
end

lemma sum_list_le_len_mul_ge (l : list ℕ) (m : ℕ) : (∀ n ∈ l, n ≤ m) → l.sum ≤ m*l.length :=
begin
  intros h,
  induction l,
  refl,
  rw [list.sum_cons, list.length_cons, mul_add, mul_one, add_comm],
  apply add_le_add,
  apply l_ih,
  intros n in_t_tl,
  specialize h n,
  apply h,
  right,
  exact in_t_tl,
  exact h l_hd (list.mem_cons_self l_hd l_tl),
end

lemma nonzero_iff_digits_len_nonzero {b n : ℕ} : 0 < n ↔ 0 < (digits b n).length :=
begin
  split,
  { intros npos,
   cases b,
   { -- base 0
     unfold digits,
     cases n,
     { linarith, },
     { unfold digits_aux_0,
       rw list.length,
       linarith,
     },
   },
   { cases b,
     { -- base 1
       unfold digits,
       unfold digits_aux_1,
       rw list.length_repeat,
       exact npos,
     },
     { -- base >= 2
       unfold digits,
       cases n,
       { linarith, },
       { unfold digits_aux,
         rw list.length_cons,
         linarith,
       },
     },
   },
  },
  { intros lenpos,
    cases b,
    { -- base 0
      unfold digits at lenpos,
      cases n,
      { unfold digits_aux_0 at lenpos,
        rw list.length at lenpos,
        exact lenpos,
      },
      { exact nat.succ_pos n, },
    },
    { cases b,
      { -- base 1
        unfold digits at lenpos,
        unfold digits_aux_1 at lenpos,
        rw list.length_repeat at lenpos,
        exact lenpos, },
      { -- base >= 2
        cases n,
        { unfold digits at lenpos,
          unfold digits_aux at lenpos,
          rw list.length at lenpos,
          exact lenpos, },
        { exact nat.succ_pos n},
      },
    },
  },
end

lemma digits_no_leading_zero {b n : ℕ} : (∀ (h : (digits b n) ≠ list.nil), (digits b n).last h ≠ 0) :=
begin
  intros h lh,
  sorry
end

lemma digits_len_le_digits_len_succ {b n : ℕ} : (digits b n).length ≤ (digits b (n + 1)).length :=
begin
  cases b,
  { -- base 0
    unfold digits,
    cases n,
    { unfold digits_aux_0,
      repeat { rw list.length },
      linarith,
    },
    { unfold digits_aux_0,
      repeat { rw list.length },
    },
  },
  { cases b,
    { -- base 1
      unfold digits,
      unfold digits_aux_1,
      repeat {rw list.length_repeat },
      linarith,
    },
    { -- base >= 2
      apply nat.strong_induction_on n,
      clear n,
      intros n IH,
      cases n,
      { rw digits_zero,
        rw list.length,
        linarith,
      },
      { sorry
      },
    },
  },
end

lemma le_digits_len_le {b n m : ℕ} :  n ≤ m → (digits b n).length ≤ (digits b m).length :=
begin
  intros h,
  cases b,
  { -- base 0
    unfold digits,
    cases n,
    { unfold digits_aux_0,
      rw list.length,
      linarith,
    },
    { cases m,
      { linarith [nat.succ_pos n] },
      { unfold digits_aux_0, 
        repeat {rw list.length},
      },
    },
  },
  { cases b,
    { -- base 1
      unfold digits,
      unfold digits_aux_1,
      repeat { rw list.length_repeat },
      exact h,
    },
    { -- base >= 2
      rw le_iff_exists_add at h,
      cases h with c hc,
      sorry
    },
  },
end

lemma div_ge_of_ge (a b : ℕ) : 0 < a → 0 < b → b ≤ a → 1 ≤ a/b :=
begin
  intros ha hb h,
  rw nat.div_eq_sub_div hb h,
  exact nat.le_add_left 1 ((a-b)/b),
end

lemma digits_ge_base_pow_len {b m : ℕ} : m > 0 → m ≥ (b + 2) ^ ((digits (b + 2) m).length - 1) :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros n IH npos,
  unfold digits at IH ⊢,
  cases n,
  { linarith, },
  { rw [digits_aux_def (b+2) (by linarith) (n.succ), list.length_cons],
    specialize IH ((n.succ)/(b+2)) (nat.div_lt_self' n b),
    cases nat.lt_or_ge n.succ (b+2),
    { have ltb := nat.div_eq_of_lt h,
      rw [ltb, digits_aux_zero, list.length],
      simp,
      linarith,
    },
    { have geb : (n.succ / (b + 2)) ≥ 1,
      exact div_ge_of_ge n.succ (b+2) npos (by linarith) h,
      specialize IH geb,
      rw nat.succ_sub_one (digits_aux (b + 2) _ (n.succ / (b + 2))).length,
      have IH' := nat.mul_le_mul_left (b+2) IH,
      rw [nat.mul_comm, <- nat.pow_succ, nat.succ_eq_add_one, nat.add_comm ((digits_aux (b + 2) _ (n.succ / (b + 2))).length - 1), <- nat.add_sub_assoc, nat.add_sub_cancel_left 1 (digits_aux (b + 2) _ (n.succ / (b + 2))).length] at IH',
      have IH'' := nat.div_mul_le_self n.succ (b+2),
      rw mul_comm at IH',
      exact le_trans IH' IH'',
      change 0 < (digits_aux (b + 2) _ (n.succ / (b + 2))).length,
      rw [<- digits, <- nonzero_iff_digits_len_nonzero],
      exact geb,
    },
    exact npos,
  },
end

lemma ten_digits_ge_base_pow_len (n : ℕ) : n > 0 → n ≥ 10 ^ ((digits 10 n).length - 1) :=
begin
  exact digits_ge_base_pow_len,
end

-- Thanks Grayson Burton for this handy lemma!!
lemma ex_pred_of_s : ∀ n > 0, ∃ m : ℕ, m.succ = n
| 0       h := absurd h dec_trivial
| (n + 1) _ := ⟨n, rfl⟩

-- this was used for the disaster lmao
lemma lt_add_lt_mul (a b c : ℕ) (hb : 1 < b) (hc : 0 < c) : a < c → a + c < b*c :=
begin
  intros h,
  have hbc : 2*c ≤ b*c,
  induction hb with k hbk,
  { rw nat.succ_eq_add_one, },
  { apply le_trans hb_ih,
    rw nat.succ_mul,
    linarith,
  },
  have hac : a + c < 2*c,
  linarith,
  linarith,
end

lemma digits_lt_base_pow_len {b m : ℕ} : m > 0 → m < (b + 2) ^ ((digits (b + 2) m).length) :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros n IH npos,
  unfold digits at IH ⊢,
  cases n,
  { linarith, },
  { rw [digits_aux_def (b+2) (by linarith) (n.succ), list.length_cons],
    specialize IH ((n.succ)/(b+2)) (nat.div_lt_self' n b),
    cases nat.lt_or_ge n.succ (b+2),
    { rw [nat.pow_add (b+2) (digits_aux (b + 2) _ (n.succ / (b + 2))).length 1, nat.div_eq_of_lt h, <- digits, digits_zero, list.length, nat.pow_zero, nat.one_mul, nat.pow_one],
      exact h,
    },
    { have divpos := div_ge_of_ge n.succ (b+2) npos (by linarith) h,
      specialize IH divpos,
      have bpos : b + 2 > 0 := by linarith,
      have IH' := nat.mul_lt_mul_of_pos_left IH bpos,
      have IH'' := nat.add_lt_add_left IH' (n.succ % (b + 2)),
      rw nat.mod_add_div n.succ (b+2) at IH'',
      sorry

      /- DISASTER
      cases ex_pred_of_s (n.succ / (b+2)) (divpos) with m exm,
      rw <- exm,
      unfold digits_aux,
      rw list.length_cons,
      have ltb := nat.mod_lt n.succ bpos,
      repeat { rw nat.pow_add },
      rw nat.pow_one,
      rw nat.mul_comm,
      rw <- nat.mul_assoc,
      rw nat.mul_comm,
      rw <- nat.mul_assoc,
      have powpos : 0 < (b + 2) * (b + 2) ^ (digits_aux (b + 2) _ (n.succ / (b + 2))).length,
      apply nat.mul_pos,
      exact bpos,
      exact nat.pos_pow_of_pos _ bpos,
      linarith,
      have hlt : n.succ % (b + 2) + (b + 2) * (b + 2) ^ (digits_aux (b + 2) _ (n.succ / (b + 2))).length < (b + 2) * (b + 2) * (b + 2) ^ (digits_aux (b + 2) _ ((m + 1) / (b + 2))).length := lt_add_lt_mul (n.succ / (b+2)) (b+2) ((b + 2) * (b + 2) ^ (digits_aux (b + 2) _ ((m + 1) / (b + 2))).length) (by linarith) powpos,
    -/
    },
    exact npos,
  },
end

-- happy function on a 4 or more digit number will result in a smaller number
lemma ten_happyfunction_lt_four_digits (n : ℕ) (R = (digits 10 n).length): (R ≥ 4) → happyfunction 2 10 n < n :=
begin
  intros hR,
  induction hR with k nk IH,
  { have h₁ : happyfunction 2 10 n ≤ 81*4,
    unfold happyfunction,
    have h₂ : ∀ dsq ∈ (list.map (λ (d : ℕ), d ^ 2) (digits 10 n)), dsq ≤ 81,
    intros dsq dsqh,
    simp at dsqh,
    cases dsqh with d' d'sqh,
    cases d'sqh with dh sqh,
    have h₃ := ten_digits_le_9 n d' dh,
    rw <- sqh,
    exact nat.pow_le_pow_of_le_left h₃ 2,
    have h₄ := sum_list_le_len_mul_ge (list.map (λ (d : ℕ), d ^ 2) (digits 10 n)) 81 h₂,
    rw list.length_map (λ (d : ℕ), d ^ 2) (digits 10 n) at h₄,
    rw H,
    exact h₄,
    have h₅ : 81 * 4 < n,
    have npos : 0 < n,
    rw [nonzero_iff_digits_len_nonzero, <- H],
    linarith,
    have h₇ := ten_digits_ge_base_pow_len n npos,
    rw <- H at h₇,
    calc (81*4) < (10^(4-1)) : by norm_num
         ... ≤ n : h₇,
    linarith,
  },
  { sorry
  },
end

def K : set ℕ := {4, 16, 37, 58, 89, 145, 42, 20}

lemma K_closed_under_happyfunction (n : ℕ) (H : n ∈ K) : happyfunction 2 10 n ∈ K :=
begin
  iterate 7 {
  cases H,
  rw H,
  unfold happyfunction,
  norm_num,
  right,
  simp,},
  have H' := set.eq_of_mem_singleton H,
  rw H',
  unfold happyfunction,
  norm_num,
  left,
  refl,
end

lemma K_closed_under_happyfunction' (n : ℕ) (H : n ∈ K) : ∀ (i : ℕ), happyfunction' 2 10 n i ∈ K :=
begin
  intros i,
  induction i with k ik,
  unfold happyfunction',
  exact H,
  unfold happyfunction',
  exact K_closed_under_happyfunction (happyfunction' 2 10 n k) ik,
end

-- 10-Sad numbers > 0 always end in the 8 number cycle {4, 16, 37, 58, 89, 145, 42, 20}
lemma ten_sad_eightnumcycle (n : ℕ) (H : sad 10 n) : ∃ (j : ℕ), ∀ (i : ℕ), (j ≤ i) → (happyfunction' 2 10 n i) ∈ K :=
begin
  sorry
end

theorem ten_happyfunction_convergence (A : ℕ) : ∃ (n > 0),  ∀ (r ≥ n), (happyfunction' 2 10 A r = 1 ∨ happyfunction' 2 10 A r ∈ K) :=
begin
  have H := happy_or_sad 10 A,
  cases H,
  cases H with n Hn,
  use n,
  split,
  sorry
end

end mainTheorem

#print happyfunction
#eval happyfunction 2 10 8

#print happyfunction'
#eval happyfunction' 2 10 7 5

#print happy
#reduce happy 10 7

#print sad
#reduce sad 10 4

end happynumber
