import Mathlib
/-- 8/9/2026 --/

example {a b : ℝ} : 2*a*b ≤ a^2 + b^2 := by
 have h : 0 ≤ a^2 - 2*a*b + b^2 := by
  rw [← sub_sq a b]
  apply sq_nonneg (a - b)
 linarith

--  Other approach
example {a b : ℝ} : 2*a*b ≤ a^2 + b^2 := by
 have h:  0 ≤ a^2 - 2*a*b + b^2
 calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
 linarith





-- #check abs_le'.mpr -- the reverse direction of the theorem

-- example {a b : ℝ} : |a*b| ≤ (a^2 + b^2)/2 := by
--  apply abs_le'.mpr

-------------------------------------------------------------------------------------------
--  # 2.4 More examples using apply and rw -----------------------------------------------
------------------------------------------------------------------------------------------

section
-- variable (R : Type*) [Ring R]

------- the min function
#check (min_le_left)
#check (min_le_right)
#check (le_min) -- not well understood
#check (le_antisymm)

-- example {a b : ℝ}: min a b = min b a := by
--  apply le_antisymm
--  . show min a b ≤ min b a
--     apply le_min



-- #  In a different approach we can remove the show tactic
example {b a : ℝ} : min a b = min b a := by
 have h : ∀ x y : ℝ, min x y ≤ min y x := by
  intro x y
  apply le_min
  apply min_le_right
  apply min_le_left

 apply le_antisymm
 apply h
 apply h

-- # Let's use the repeat tactic
example {a b : ℝ} : min a b = min b a := by
 apply le_antisymm
 repeat
   apply le_min
   apply min_le_right
   apply min_le_left

   -- # max function

#check max
#check max_le

example {a b c : ℝ} : min (min a b ) c  = min a (min b c) := by
 apply le_antisymm


end
