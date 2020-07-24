import tactic
import data.nat.digits
import logic.basic
import data.list

namespace happynumber

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
lemma ten_happyfunction_eq_permute_digits (p : ℕ) (n n' : ℕ) (P : (digits 10 n) ~ (digits 10 n')) : happyfunction p 10 n = happyfunction p 10 n' :=
begin
  unfold happyfunction,
  have h := list.perm.map (λ (d : ℕ), d^p) P,
  have h' := list.perm.sum_eq h,
  exact h',
end

lemma ten_happyfunction'_eq_permute_digits (p i : ℕ) (n n' : ℕ) (P : (digits 10 n) ~ (digits 10 n')) : happyfunction' p 10 n i = happyfunction' p 10 n' i :=
begin
  sorry
end

-- permuting a 10-happy number's digits will result in another happy number
lemma ten_happy_permute_ten_happy (n : ℕ) (H : happy 10 n) (n' : ℕ) (P : (digits 10 n) ~ (digits 10 n')) : happy 10 n' :=
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

lemma ne_zero_iff_digits_ne_nil (b n : ℕ) : n ≠ 0 ↔ digits b n ≠ list.nil :=
begin
  split,
  { intros hn hd,
    cases n,
    { contradiction },
    { have h := of_digits_digits b n.succ,
      rw hd at h,
      contradiction,
    },
  },
  { contrapose!,
    intros h,
    rw h,
    exact digits_zero b,
  },
end

lemma ne_zero_iff_digits_len_ne_zero (b n : ℕ) : n ≠ 0 ↔ (digits b n).length ≠ 0 :=
begin
  rw [ne_zero_iff_digits_ne_nil b n, not_iff_not],
  symmetry',
  exact list.length_eq_zero,
end

lemma digits_ge_base_pow_len (b m : ℕ) : m ≠ 0 → m ≥ (b + 2) ^ ((digits (b + 2) m).length - 1) :=
begin
  apply nat.strong_induction_on m,
  clear m,
  intros n IH npos,
  unfold digits at IH ⊢,
  cases n,
  { contradiction, },
  { rw [digits_aux_def (b+2) (by linarith) (n.succ), list.length_cons],
    specialize IH ((n.succ)/(b+2)) (nat.div_lt_self' n b),
    cases nat.lt_or_ge n.succ (b+2),
    { rw [nat.div_eq_of_lt h, digits_aux_zero, list.length],
      exact nat.succ_pos n },
    { have geb : (n.succ / (b + 2)) ≥ 1 := nat.div_pos h (by linarith),
      specialize IH (by linarith [geb]),
      rw nat.succ_sub_one,
      have IH' := nat.mul_le_mul_left (b+2) IH,
      rw [nat.mul_comm, <- nat.pow_succ, nat.succ_eq_add_one] at IH',
      rw nat.add_comm ((digits_aux (b + 2) _ (n.succ / (b + 2))).length - 1) at IH',
      rw <- nat.add_sub_assoc at IH',
      { rw nat.add_sub_cancel_left 1 (digits_aux (b + 2) _ (n.succ / (b + 2))).length at IH',
        have IH'' := nat.div_mul_le_self n.succ (b+2),
        rw mul_comm at IH',
        exact le_trans IH' IH'' },
      { change 0 < (digits_aux (b + 2) _ (n.succ / (b + 2))).length,
        rw nat.pos_iff_ne_zero,
        rw [<- digits, <- ne_zero_iff_digits_len_ne_zero],
        linarith [geb] } },
    rwa nat.pos_iff_ne_zero }
end

lemma ten_digits_ge_base_pow_len (n : ℕ) : n ≠ 0 → n ≥ 10 ^ ((digits 10 n).length - 1) :=
begin
  exact digits_ge_base_pow_len 8 n,
end

lemma digits_one_less (b m : ℕ) : m > 0 → (digits (b+2) m).length = (digits (b+2) (m/(b+2))).length + 1 :=
begin
  intros hm,
  unfold digits,
  conv_lhs { rw digits_aux_def (b+2) (by linarith) m hm },
  rw list.length_cons,
end

-- happyfunction n is less than 81*(number of digits in n)
lemma ten_happyfunction_le (n : ℕ) : happyfunction 2 10 n ≤ 81*(digits 10 n).length :=
begin
  unfold happyfunction,
  have hdsq : ∀ dsq ∈ (list.map (λ (d : ℕ), d ^ 2) (digits 10 n)), dsq ≤ 81,
  intros dsq dsqin,
  rw list.mem_map at dsqin,
  cases dsqin with d' hd',
  cases hd' with dh sqh,
  have dle := ten_digits_le_9 n d' dh,
  rw <- sqh,
  exact nat.pow_le_pow_of_le_left dle 2,
  have hle := sum_list_le_len_mul_ge (list.map (λ (d : ℕ), d ^ 2) (digits 10 n)) 81 hdsq,
  rw list.length_map (λ (d : ℕ), d ^ 2) (digits 10 n) at hle,
  exact hle,
end

lemma helper_lt (a : ℕ) : 81*(a + 4) < 10^(a + 3) :=
begin
  induction a with k ak,
  { norm_num },
  { repeat { rw nat.succ_add },
    rw nat.mul_succ,
    rw nat.pow_succ,
    linarith,
  },
end

-- happy function on a 4 or more digit number will result in a smaller number
lemma ge_four_digits_dec (n : ℕ) : 4 ≤ (digits 10 n).length → happyfunction 2 10 n < n :=
begin
  intros hdig,
  have npos : n ≠ 0,
  rw ne_zero_iff_digits_len_ne_zero 10,
  linarith,
  have hge := digits_ge_base_pow_len 8 n npos,
  norm_num at hge,
  have hle := ten_happyfunction_le n,
  set R := (digits 10 n).length with ←h,
  suffices : 81*R < 10^(R-1),
  { linarith },
  rw le_iff_exists_add at hdig,
  cases hdig with c hc,
  rw hc,
  norm_num,
  rw [add_comm 4 c, add_comm 3 c],
  exact helper_lt c,
end

lemma ge_four_digits_le_digits_len (n : ℕ) : 4 ≤ (digits 10 n).length → (digits 10 (happyfunction 2 10 n)).length ≤ (digits 10 n).length :=
begin
  intros h,
  have dec := ge_four_digits_dec n h,
  exact le_digits_len_le 10 (happyfunction 2 10 n) n (by linarith [dec]),
end

-- eventually, happyfunction on n is less than 4 digits long
lemma eventually_lt_four_digits (n : ℕ) : ∃ (a : ℕ), (digits 10 (happyfunction' 2 10 n a)).length < 4 :=
begin
  sorry
end

-- eventually, happyfunction on n is less than or equal to 162
lemma eventually_le (n : ℕ) : ∃ (a : ℕ), happyfunction' 2 10 n a ≤ 162 :=
begin
  sorry
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
#eval happyfunction 2 10 999

#print happyfunction'
#eval happyfunction' 2 10 7 5

#print happy
#reduce happy 10 7

#print sad
#reduce sad 10 4

end happynumber
