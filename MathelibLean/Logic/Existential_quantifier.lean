import Mathlib

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
 use 2.5
 norm_num


example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
 have h1 : 2 < (5: ℝ) / 2 := by norm_num
 have h2 : (5 : ℝ) / 2 < 3 := by norm_num
 use ( 5 : ℝ ) / 2, h1,h2


example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
 have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
 use 5 / 2

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
 have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
 ⟨5/2, h⟩

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
 ⟨5/2,  by norm_num⟩

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
 ∀ x, f x < a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
 ∀ x, a < f x

def FnHasUb (f : ℝ → ℝ) :=
 ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
 ∃ a, FnLb f a


-- # the sum of two upper bound functions is upper bound
example  (f g : ℝ → ℝ) (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb ( fun x ↦ f x + g x) := by
 rcases ubf with ⟨a, ubfa⟩
 rcases ubg with ⟨b, ubgb⟩
 simp only [FnHasUb, FnUb] at *
 use a + b
 intro x
 apply add_lt_add
 · apply ubfa
 apply ubgb

-- # The sum of two lower bound functions is lower bound
example (f g : ℝ → ℝ) (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
 rcases lbf with ⟨a, lbfa⟩
 rcases lbg with ⟨b, lbgb⟩
 simp only [FnHasLb, FnLb] at *
 use a + b
 intro x
 apply add_lt_add
 · apply lbfa
 apply lbgb

example {f: ℝ → ℝ} {c : ℝ} (ubf : FnHasUb f) (cnneg : 0 ≤ c) : FnHasUb fun x ↦ c * f x  := by
 rcases ubf with ⟨a, ubfa⟩
 simp only [FnHasUb, FnUb] at *
 use c*a
 intro x


-- # The theorem FnUb_add has to be stated in order to be used in the next examples

theorem FnUb_add {f g : ℝ → ℝ} (h₀ : FnUb f a) (h₁ : FnUb g b) : FnUb (fun x ↦ f x + g x) (a+b) := by
 intro x
 dsimp
 simp only [FnUb] at *
 apply add_lt_add
 · apply h₀
 apply h₁

-- # The sum of two function who have upper bound is function having an upper bound

-- # Using `rintro`
-- # rintro is  a combination between rcases and intro
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
 rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
 exact ⟨a+b, FnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, FnUb_add ubfa ubgb⟩

-- # Using the `obtain` tactic
example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
 obtain ⟨a, ubfa⟩ := ubf
 obtain ⟨b, ubgb⟩ := ubg
 exact ⟨a + b, FnUb_add ubfa ubgb⟩

--  # Other aproaches
-- # Aproach 1 using `cases` and `case` tactic
example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
 cases ubf
 case intro a ubfa =>
   cases ubg
   case intro b ubgb =>
    exact ⟨a + b, FnUb_add ubfa ubgb⟩

-- # Aproach 2 : Using `cases` and `next` tactics
example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦  f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
     exact ⟨a + b, FnUb_add ubfa ubgb⟩

-- # Aproach 3
example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
 match ubf, ubg with
  |  ⟨a, ubfa⟩ , ⟨b, ubgb⟩  =>
     exact ⟨a + b, FnUb_add ubfa ubgb⟩

-- # Aproach 4
example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
 match ubf, ubg with
  | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
    ⟨a+b, FnUb_add ubfa ubgb⟩

-- # The product of two squares is a square in any commutative ring
variable {α : Type*} [CommRing α]

def SumOfSquare (x : α) :=
 ∃ a b, x = a^2 + b^2


theorem SumOfSquares_mul {x y : α} (sosx : SumOfSquare x) (sosy : SumOfSquare y) : SumOfSquare (x * y) := by
 rcases sosx with ⟨a, b, eqx⟩
 rcases sosy with ⟨c, d, eqy⟩
 simp only [SumOfSquare]
 rw [eqx, eqy]
 use a * c - b * d, a * d + b * c
 ring

theorem SumOfSquares_mul' {x y : α} (sosx : SumOfSquare x) (sosy : SumOfSquare y) : SumOfSquare (x * y) := by
 rcases sosx with ⟨a, b, rfl⟩
 rcases sosy with ⟨c, d, rfl⟩
 use a * c - b * d, a * d + b * c
 ring

-- # Divisibility is an example of an exists statments
example {a b c : ℕ} (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
 rcases divab with ⟨q, exq⟩
 rcases divbc with ⟨p, exp⟩
 rw [exp, exq]
 use q * p; ring

example {a b c : ℕ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
 rcases divab with ⟨q, exq⟩
 rcases divac with ⟨p, exp⟩
 use p + q;
 linarith


open Function
example {c : ℝ} : Surjective fun x ↦ x + c := by
 intro x
 use x -c
 dsimp; ring

example {c : ℝ} : Surjective fun x ↦ c * x := by
 intro y
 use y * c⁻¹
 dsimp
 ring_nf

-- # `field_simp` tactic is used to remove denominators
example (x y : ℝ) (h : x - y ≠ 0) : (x^2 - y^2) / (x - y) = x + y:= by
 field_simp [h]
 ring


example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
 rcases h 2 with ⟨x, hx⟩
 use x
 rw [hx]
 norm_num

-- # The composition of two surjective functions is surjective
variable {α : Type*} {β : Type*} {γ : Type*}
variable {f : α → β} {g : β → γ}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
 intro x
 dsimp
 simp only [Surjective] at *
