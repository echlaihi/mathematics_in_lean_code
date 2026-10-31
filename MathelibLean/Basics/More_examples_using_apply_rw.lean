import Mathlib

#check  min_le_left
#check min_le_right
#check le_min

example {a b : ℝ} : min a b  = min b a := by
 apply le_antisymm
 show min a b ≤ min b a
 apply le_min
 . apply min_le_right
 apply min_le_left

 show min b a ≤ min a b
 apply le_min
 . apply min_le_right
 apply min_le_left

example {a b : ℝ} : min a b = min b a := by
 have h : ∀ x y : ℝ, min x y ≤ min y x := by
   intro x y
   apply le_min
   apply min_le_right
   apply min_le_left

 apply le_antisymm
 apply h
 apply h

-- # Using the repeat tactic
example {a b : ℝ} : min a b  = min b a := by
 apply le_antisymm
 repeat
  apply le_min
  apply min_le_right
  apply min_le_left

-- # Let's see the function max
#check max_le
example {a b : ℝ} : max a b  = max b a := by
 have h : ∀ x y : ℝ, max a b ≤ max b a := by
  intro x y
  apply max_le

example {a b c : ℝ} : min (min a b) c  = min a (min b c) := by
 apply le_antisymm
 apply le_min

theorem min_add_le_min_add_add {a b c : ℝ} : min a b + c ≤ min (a + c) (b + c) := by
 apply le_min
 apply add_le_add
 apply min_le_left
 apply le_rfl
 apply add_le_add
 apply min_le_right
 apply le_rfl

theorem min_add_add_le_min_add {a b c : ℝ} : min (a + c) (b + c) ≤ min a b + c := by
--  rw [add_zero min (a + c) (b + c)]
--  nth_rewrite 3 [← add_← add_neg_cancel_right c]


-- # More short way
-- theorem aux' {a b c : ℝ} : min a b + c ≤ min (a + c) (b + c) := by
--  repeat
  -- apply le_min
  -- apply add_le_add
  -- apply min_le_left
  -- apply add_le_add





example {a b c : ℝ} : min a b + c = min (a + c) (b + c) := by
--  apply le_antisymm

#check (abs_add_le)
example {a b : ℝ} : |a| - |b| ≤ |a - b| := by
 nth_rewrite 1 [← add_neg_cancel_right a b, ← add_neg_cancel_right (|a - b|) (|b|)]
 apply sub_le_sub
 rw [add_assoc]
 nth_rewrite 2 [add_comm]
 rw [← add_assoc]
 apply abs_add_le (a + -b) b
 apply le_rfl


-- # The divisibility operation
#check dvd_trans
#check dvd_mul_of_dvd_left
#check dvd_mul_of_dvd_right
#check dvd_mul_left


example {x y z : ℕ} (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z := by
 apply dvd_trans h₀ h₁

example {x y z : ℕ} : x ∣ y * x * z := by
 apply dvd_mul_of_dvd_left
 apply dvd_mul_left


example {x : ℕ} : x ∣ x^2 := by
 apply dvd_mul_left

example {x w z : ℕ} (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 := by
 apply dvd_add
 apply dvd_add
 rw [mul_comm, mul_assoc]
 apply dvd_mul_right
 apply dvd_mul_left
 have h' : w ∣ w^2 := by
  apply dvd_mul_left
 apply dvd_trans h h'



variable (m n : ℕ)
#check (Nat.gcd_zero_right)
#check (Nat.gcd_zero_left)
#check (Nat.lcm_zero_right)
#check (Nat.lcm_zero_left)

example : Nat.gcd m n = Nat.gcd n m := by
 apply Nat.dvd_antisymm
 apply Nat.dvd_gcd
 apply Nat.gcd_dvd_right
 apply Nat.gcd_dvd_left
 apply Nat.dvd_gcd
 apply Nat.gcd_dvd_right
 apply Nat.gcd_dvd_left
