import tactic
import data.nat.digits

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
  simp at hc,
  rw hc,
  exact H,
  rw nat.add_succ at hc,
  rw hc,
  unfold happyfunction',
  specialize ck (j+k),
  simp at ck,
  rw ck,
  --unfold happyfunction,
  simp,
end

-- for base b, after reaching 1, will stay 1
lemma happily_ever_after (b : ℕ) (n : ℕ) (j: ℕ) : happyfunction' 2 b n j = 1 → ∀ i, (j ≤ i) → happyfunction' 2 b n i = 1 :=
begin
  intros H i hi,
  rw le_iff_exists_add at hi,
  cases hi with c hc,
  induction c with k ck generalizing i,
  simp at hc,
  rw hc,
  exact H,
  rw nat.add_succ at hc,
  rw hc,
  unfold happyfunction',
  specialize ck (j+k),
  simp at ck,
  rw ck,
  --exact happyfunction_one' 2 b,
  simp,
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
  unfold happyfunction,
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
@[simp]
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

-- for b=10, permuting the digits won't make a difference
lemma happyfunction_eq_permute_digits_ten (p : ℕ) (n n' : ℕ) (P : (digits 10 n) ~ (digits 10 n')) : happyfunction p 10 n = happyfunction p 10 n' :=
begin
  sorry
end

-- n is 10-happy iff n*10 is 10-happy
lemma ten_happy_times_ten (n : ℕ) : happy 10 n ↔ happy 10 (n*10) :=
begin
  sorry
end

-- 10^m is always a 10-happy number
lemma ten_happy_pow_ten (m : ℕ) : happy 10 (10^m) :=
begin
  use 1,
  unfold happyfunction',
  sorry
end

-- 10^n is always a b-happy number
lemma happy_pow_ten (n : ℕ) : happy 10 (10^n) :=
begin
  sorry
end

-- permuting a 10-happy number's digits will result in another happy number
lemma ten_happy_permute_ten_happy (b : ℕ) (n : ℕ) (H : happy b n) (n' : ℕ) (P : (digits b n) ~ (digits b n')) : happy b n' :=
begin
  sorry
end

-- happy function on a 4 digit number will result in a smaller number
lemma ten_happyfunction_lt_four_digits (n : ℕ) (H : (digits 10 n).length ≥ 4) : happyfunction 2 10 n < n :=
begin
  sorry
end

def K : set ℕ := {4, 16, 37, 58, 89, 145, 42, 20}
-- 10-Sad numbers > 0 always end in the 8 number cycle {4, 16, 37, 58, 89, 145, 42, 20}
theorem ten_sad_eightnumcycle (n : ℕ) (H : sad 10 n) : ∃ (j : ℕ), ∀ (i : ℕ), (j ≤ i) → (happyfunction' 2 10 n i) ∈ K :=
begin
  sorry
end

#print happyfunction
#eval happyfunction 2 10 8

#print happyfunction'
#eval happyfunction' 2 10 7 5

#print happy
#reduce happy 10 7

end happynumber
