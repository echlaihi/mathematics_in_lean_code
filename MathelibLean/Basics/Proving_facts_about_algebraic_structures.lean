import Mathlib

variable { α : Type* } [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check le_refl
#check le_trans
#check le_antisymm

#check x < y
#check lt_irrefl
#check lt_trans
#check lt_of_le_of_lt
#check lt_of_lt_of_le


example : x < y ↔ x ≤ y ∧ x ≠ y :=
 lt_iff_le_and_ne

variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y  -- #  stands for the greatest lower bound for x and y,infimum, meet
#check inf_le_left
#check inf_le_right
#check le_inf

#check x ⊔ y -- # stands for the least upper bound for x and y, supremum, join
#check le_sup_left
#check le_sup_right
#check sup_le

example : x ⊓ y = y ⊓ x := by
 apply le_antisymm
 apply le_inf
 apply inf_le_left
 apply inf_le_right




--  have
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
 apply le_antisymm
 apply le_inf
 apply le_inf
 apply inf_le_left

example : x ⊔ y = y ⊔ x := by
 sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
 sorry
