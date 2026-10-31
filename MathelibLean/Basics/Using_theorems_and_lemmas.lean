import Mathlib

-- variable {a b c : ℝ} (h : a ≤  b) (h' : b ≤ c)

-- #check (le_refl)
-- #check (le_trans)
-- #check (le_refl a)

-- #check (le_refl a)
-- #check (le_trans h h')

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
 apply le_trans
 . apply h₀
 . apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
 apply le_trans h₀
 apply h₁

example (x : ℝ) : x ≤ x := by
 apply le_refl x

example (x : ℝ) : x ≤ x :=
 le_refl x

-- # More theorem libraries
#check (le_refl)
#check (le_trans)
#check (lt_of_le_of_lt)
#check (lt_of_lt_of_le)

example {a b c d e : ℝ} (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d) (h₃ : d ≤ e) : a ≤  e := by
  linarith

-- # A different aproach
example {a b c d e : ℝ} (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d) (h₃ : d ≤ e) : a ≤ e := by
 sorry

example {a b d : ℝ} (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
 linarith

example {a b c : ℝ} (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + Real.exp b ≤ 3 * a + Real.exp c := by
 linarith [Real.exp_le_exp.mpr h']

#check (Real.exp_le_exp)
#check (Real.exp_lt_exp)
#check (Real.log_le_log)
#check (Real.log_lt_log)

-- # Inequialities and addition
#check (add_le_add)
#check (add_lt_add_left)
#check (add_lt_add_right)
#check (add_lt_add_of_le_of_lt)
#check (add_lt_add_of_lt_of_le)
#check (add_nonneg)
#check (add_pos)
#check (add_pos_of_pos_of_nonneg)
#check (Real.exp_pos)


-- # Inequalities and multiplication
#check (mul_le_mul_of_nonneg)
#check (mul_le_mul)

-- # If h : A ↔ B then h.mpr means B → A and h.mp means A → B
--  mp stands for modulus ponens
example (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
 rw [Real.exp_le_exp]
 exact h

example {a b c d e : ℝ} (h₀ : a ≤ b) (h₁ : c < d) : a + Real.exp c + e <b +  Real.exp d + e := by
 have h : Real.exp c < Real.exp d := by
  rw [Real.exp_lt_exp]

example {a b c d e} (h₀ : a ≤ b) (h₁ : c < d) : a + Real.exp c + e <b +  Real.exp d + e := by
 apply add_lt_add_of_lt_of_le
 . apply add_lt_add_of_le_of_lt h₀
   apply Real.exp_lt_exp.mpr h₁
 apply le_refl


example {d e c a : ℝ} (h₀ : d ≤ e) : c + Real.exp (a + d) ≤ c + Real.exp (a + e) := by
 have h : Real.exp (a + d) ≤ Real.exp (a + e) := by
  apply Real.exp_le_exp.mpr
  . apply add_le_add

  -- apply add_le_add

example : (0 : ℝ) < 1 := by norm_num

example {a b : ℝ} (h : a ≤ b) : Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) := by
 have h₀ : 0 < 1 + Real.exp a := by

 apply Real.log_le_log h₀

example {a : ℝ} : 0 ≤ a^2 := by
 exact sq_nonneg a

example {a : ℝ} : 0 ≤ a^2 := by
 apply sq_nonneg a

example (h : a ≤ b) : c - Real.exp b ≤ c - Real.exp a := by
 have h' : - Real.exp b ≤ - Real.exp a := by
  apply neg_le.mpr
  rw [neg_neg]
  apply Real.exp_le_exp.mpr
  exact h
 apply add_le_add
 . apply le_refl
 . exact h'

example (h : a ≤ b) : c - Real.exp b ≤ c - Real.exp a := by
 apply Real.exp_le_exp.mpr at h
 linarith

example {a b : ℝ} : 2 * a * b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 + b^2 - 2 * a * b := by
   rw [← sub_sq']
   apply sq_nonneg (a-b)

  linarith

-- # Chalenge
example {a b : ℝ}: |a*b| ≤ (a^2 + b^2)/2 := by
 sorry
