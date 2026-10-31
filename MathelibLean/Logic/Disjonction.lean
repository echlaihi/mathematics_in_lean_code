import Mathlib

-- # to prove A or B we prove one of them
-- # we use the tactic left and right

variable {x y : ℝ}
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
 left
 have h' : x ^2 ≥ 0 := by
   apply sq_nonneg
 apply lt_of_le_of_lt h' h

-- # This is how the previous statement is proven in the book
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
 left
 linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
 right
 have h' : x ^ 2 ≥ 0 := by
  apply sq_nonneg
 linarith

-- # This is hwo the previous statement is proved in the book
example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
 right
 linarith [pow_two_nonneg x]

-- # `introduction left` and `introduction right` tactic
example (h : y > 0) : y > 0 ∨ y < -1 :=
 Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
 Or.inr h

example : x < |y| → x < y ∨ x < -y := by
 intro h'
 rcases le_or_gt 0 y with h | h -- # The tactic here tell lean to do a proof by spliting cases
 · left
   rw [abs_of_nonneg h] at h'
   exact h'
 right
 rw [abs_of_neg h] at h'
 exact h'

-- # This how the previous example is proven in the book
example : x < |y| → x < y ∨ x < -y := by
 rcases le_or_gt 0 y with h | h
 intro h'
 left
 rw [abs_of_nonneg] at h'
 exact h'
 exact h
 intro h'
 right
 rw [abs_of_neg] at h'
 exact h'
 exact h

-- # Let's see the computer scientists pattern-matching syntax
example : x < |y| → x < y ∨ x < -y := by
 cases le_or_gt 0 y
 case inl h =>
  rw [abs_of_nonneg h]
  intro h; left; exact h
 case inr h =>
  rw [abs_of_neg h]
  intro h; right; exact h

-- # inl and inr stands for intro left intro right
-- # Using case we can prove the specific case we want
-- # in the order we shoose

example : x < |y| → x < y ∨ x < -y := by
 cases le_or_gt 0 y
 next h =>
   rw [abs_of_nonneg h]
   intro h;left; exact h
 next h =>
   rw [abs_of_neg h]
   intro h; right; exact h

-- # This is also a different computer scientist's pattern-matching
example : x < |y| → x < y ∨ x < -y := by
 match le_or_gt 0 y with
 | Or.inl h =>
   rw [abs_of_nonneg h]
   intro h; left; exact h
 | Or.inr h =>
   rw [abs_of_neg h]
   intro h; right; exact h

namespace MyAbs

-- # This is my proof
theorem le_abs_self (x : ℝ) : x ≤ |x| := by
 rcases lt_or_ge 0 x with h | h
 · rw [abs_of_pos]
   exact h
 rw [abs_of_nonpos]
 have : 0 ≤ -x := by
  rw [← neg_zero]; linarith
 linarith
 exact h

theorem le_abs_self' (x : ℝ) : x ≤ |x| := by
 rcases le_or_gt 0 x with h | h
 · rw [abs_of_nonneg]
   exact h
 rw [abs_of_nonpos]
 have : 0 ≤ -x := by
   rw [le_neg, neg_zero]
   apply le_of_lt
   exact h
 apply le_of_lt at h
 apply le_trans h this
 apply le_of_lt
 exact h


theorem neg_le_self (x : ℝ) : -x ≤ |x| := by
 rcases lt_or_ge x 0 with h | h
 · rw [abs_of_neg h]
 rw [abs_of_nonneg h]
 linarith


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
 rcases lt_or_ge 0 x with h | h
 rcases lt_or_ge 0 y with h' | h'
 rw [abs_of_nonneg, abs_of_nonneg, abs_of_nonneg]
 linarith; linarith; linarith
 rw [abs_of_nonpos h', abs_of_pos h, ]

theorem abs_add' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
 by_contra
 rw [not_le] at this

theorem le_abs' : x < |y| ↔ x < y ∨ x < -y := by
 rcases lt_or_ge 0 y with h | h
 constructor
 intro h'
 rw [abs_of_pos] at h'
 left
 exact h'
 exact h
 intro h'
 rcases h' with d | d
 rw [abs_of_pos]
 exact d
 exact h


example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ 0 < x := by
 rcases lt_or_ge 0 x with h' | h'
 ·right
  exact h'
 left
 apply lt_of_le_of_ne
 ·exact h'
 exact h

-- # This is how the second example is proved in the book
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ 0 < x := by
 rcases lt_trichotomy x 0 with xlt | xeq | xgt
 ·left
  exact xlt
 · contradiction
 · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
 rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
 · rw [mul_assoc]
   apply dvd_mul_right
 rw [← mul_assoc, mul_comm n m, mul_assoc]
 apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y^ 2 + 1) : z > 0 := by
 obtain ⟨a, b, hab⟩ := h
 rcases hab with d | d


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
 rw [← mul_one 1, ← sq, ← zero_add (1^2)] at h
 apply sub_eq_of_eq_add at h
 rw [sq_sub_sq] at h
 rw [mul_eq_zero] at h
 rcases h with d | d
 · right
   linarith
 left
 linarith



example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x= y ∨ x = -y := by
 rw [← zero_add (y^2)] at h
 apply sub_eq_of_eq_add at h
 rw [sq_sub_sq] at h
 rw [mul_eq_zero] at h
 rcases h with d | d
 · right
   linarith
 left
 linarith

example (P : Prop) : ¬ ¬P → P := by
 push Not
 intro h
 exact h

example (P : Prop) : ¬¬P → P := by
 intro h
 cases em P -- # em is the abriviation of excluded middle
 · assumption
 · contradiction

example (P : Prop) : ¬¬P → P := by
 intro h
 by_cases h' : P
 · assumption
 contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
 constructor
 intro h
 by_cases h' : P
 right
 apply h
 exact h'
 left
 exact h'
 intro h
 by_cases hd : P
 intro k
 rcases h with c | c
 contradiction
 exact c
 intro h
 contradiction
