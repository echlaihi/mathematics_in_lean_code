import Mathlib
-- # 2.2 Proving Identities in Algebraic Structures
-- # the ring axioms --/
-- #check (add_assoc)
-- #check (add_comm)
-- #check (zero_add)
-- #check (neg_add_cancel)
-- #check (mul_assoc)
-- #check (mul_one)
-- #check (one_mul)
-- #check (mul_add)
-- #check (add_mul)

variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a*a + 2*a*b + b*b := by
 ring

example : (a + b) * (a - b) = a^2 - b^2 := by
 ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2*d*a := by
 rw [hyp', mul_comm d a, mul_comm a d, ← two_mul (d * a), ← mul_assoc] at hyp
 exact hyp

namespace MyRing
variable {R : Type*} [Ring R]


theorem add_zero (a : R) : a + 0  = a := by
 rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by
 rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

theorem neg_add_cancel_left' (a b : R) : -a + (a + b) = b := by
 rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right' (a b : R) : a + b + -b = a := by
 rw [add_assoc, add_neg_cancel, add_zero]

-- # Let's prove the following using the two previous theorems
theorem add_left_cancel' {a b c : R} (h : a + b = a + c) : b = c := by
--  rw [← neg_add_cancel_left' a b, h, ← add_assoc, neg_add_cancel, zero_add]
  rw [← zero_add b, ← neg_add_cancel a, add_assoc, h, ← add_assoc, neg_add_cancel, zero_add]

theorem add_right_cancel' {a b c : R} (h : b + a = c + a) : b = c := by
 rw [← add_neg_cancel_right' b a, h, add_assoc, add_neg_cancel, add_zero]

-- #  Try again with only three rewrites

theorem mul_zero (a : R) : a * 0  = 0 := by
 have h : a * 0 + a * 0 = a * 0 + 0 := by
  rw [← mul_add, zero_add, add_zero]
 apply add_left_cancel' h

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a  = 0 * a + 0 := by
   rw [← add_mul, add_zero, add_zero]
  apply add_left_cancel' h


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← zero_add b, ← neg_add_cancel a, add_assoc, h, add_zero]

theorem eq_neg_off_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
 rw [← add_zero a, ← add_neg_cancel b, ← add_assoc, h, zero_add]

theorem neg_zero : (-0 : R) = 0 := by
 apply neg_eq_of_add_eq_zero
 rw [zero_add]

example (a b : R) : a - b  = a + -b := by
  rw [sub_eq_add_neg]

example (a b : ℝ) : a - b  = a + -b := by
 rfl

example (a b : ℝ) : a - b = a + -b :=
 rfl

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
 norm_num

theorem one_add_one_eq_two' : 1 + 1 = (2 : R) := by
 rw [← two_mul, mul_one]

theorem two_mul (a : R) : 2*a = a + a := by
 rw [← one_add_one_eq_two, add_mul, one_mul]
end MyRing

-- # The notion of group
variable (A : Type*) [AddGroup A]

#check (add_assoc)
#check (zero_add)
#check (neg_add_cancel)

-- # In case the Additive group is commutative we use
variable (B : Type*) [AddCommGroup B]

  -- # In case of the Multiplicative group it is defined as followed
variable (C : Type*) [Group C]

-- the axioms of a multiplicative group
#check (mul_assoc)
#check (one_mul)
#check (inv_mul_cancel)

-- # Try to redo this theorem later
theorem mul_inv_cancel' (a : C) : a * a⁻¹ = 1 := by
  nth_rewrite 1[ ← one_mul a, ← inv_mul_cancel a⁻¹, mul_assoc  (a⁻¹⁻¹), inv_mul_cancel, mul_one, inv_mul_cancel (a⁻¹)]
  rfl

theorem mul_one'(a : C) : a * 1 = a := by
 rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]


theorem mul_inv_rev' (a b : C) : (a*b)⁻¹ = b⁻¹*a⁻¹ := by
  rw [← mul_one (b⁻¹*a⁻¹), ← mul_inv_cancel (a*b), ← mul_assoc, ← mul_assoc, mul_assoc b⁻¹, inv_mul_cancel, mul_one, inv_mul_cancel, one_mul ]
