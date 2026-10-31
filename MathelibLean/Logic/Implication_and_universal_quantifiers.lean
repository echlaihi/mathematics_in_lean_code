import Mathlib

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε < 1 → |x| < ε → |y| < ε → |x * y| < ε
#check ∀ x y ε : ℝ , (0 < ε ∧ ε < 1) ∧ (|x| < ε ∧ |y| < ε ) → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε < 1 → |x| < ε → |y| < ε → |x * y| < ε := by

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ < 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma3 :
∀ {x y ε : ℝ}, 0 < ε → ε < 1 → |x| < ε → |y| < ε → |x * y| < ε := by
 intro x y ε epos ele1 xlt ylt
 calc
   |x * y| = |x| * |y| := by rw [abs_mul]
    _ < |x| * ε := by apply Real.mul_lt_mul_right (|x|) (|y|) ε

    _ < 1 * ε := by apply mul_lt_mul_right
    _ < ε := by sorry


def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
 ∀  x,  f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
 ∀ x, a ≤ f x

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
 intro x
 dsimp
 apply add_le_add
 · apply hfa
 apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
 intro x
 dsimp
 apply add_le_add
 · apply hfa
 apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x + g x) 0 := by
  intro x
  dsimp
  apply add_nonneg
  · apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) : FnUb (fun x ↦ f x * g x) (a * b) := by
 intro x
 dsimp
 simp only [FnUb, FnLb] at *
 apply mul_le_mul_of_nonneg'
 · apply hfa
 · apply hgb
 · apply nng
 apply nna


variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R][IsOrderedCancelAddMonoid R]

-- # A monoid is an algebraic structure with identity element and a binary associative operation

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
 ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) : FnUb' (fun x ↦ f x+g x) (a + b) :=
fun x ↦ add_le_add (hfa x) (hgb x)

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
 @h

-- # Let's prove that the sum of two monotone function is monotone
example (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
 intro a b aleb
 apply add_le_add
 · apply mf aleb
 apply mg aleb

-- # this is a short way to proove the previous theorem
example (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
 fun _a _b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {f : ℝ → ℝ} {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
 intro a b aleb
 dsimp
 apply mul_le_mul_of_nonneg_left
 · apply mf aleb
 apply nnc

-- # the composition of monotone functions is monotone
example {f g : ℝ → ℝ} (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
 intro a b aleb
 dsimp
 apply mf
 apply mg aleb

-- # About even and odd function
def FnEven (f : ℝ → ℝ) : Prop :=
 ∀ x,   f x  = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
 ∀ x, f x = - f (- x)

-- # The sum of two even function is even
example {f g : ℝ → ℝ} (hf : FnEven f) (hg : FnEven g) : FnEven fun x ↦ f x + g x := by
 intro x
 dsimp
 simp only [FnEven] at *
 rw [hf, hg]

--  # this is how it is proved in the book
example {f g : ℝ → ℝ} (hf : FnEven f) (hg : FnEven g) : FnEven fun x ↦  f x + g x := by
 intro x
 calc
  (fun x ↦ f x + g x ) x = f x + g x := rfl
  _ = f (-x) + g (-x) := by rw [hf, hg]

-- # The product of two odd functions is even function
example {f g : ℝ → ℝ} (hf : FnOdd f) (hg : FnOdd g) : FnEven fun x ↦ f x * g x := by
 intro x
 dsimp
 simp only [FnOdd] at *
 rw [hf, hg, neg_mul_neg]

-- # The product of an odd function and an even function is odd
example {f g : ℝ → ℝ} (hf : FnOdd f) (hg : FnEven g) : FnOdd fun x ↦ f x * g x := by
 intro x
 dsimp
 simp only [FnOdd, FnEven] at *
 rw [hf, hg, neg_mul]

-- # The composition of an even and odd function is even
example {f g : ℝ → ℝ} (hf : FnEven f) (hg : FnOdd g) : FnEven fun x ↦ f (g x) := by
 intro x
 dsimp
 simp only [FnEven, FnOdd] at *
 rw [hg, hf, neg_neg]


variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

variable {a b : R} {f g : α → R}
theorem FnUb_add (hfa : FnUb' f a) (hgb : FnUb' g b) : FnUb' (fun x ↦ f x + g x) (a + b) :=
 fun x ↦ add_le_add (hfa x) (hgb x)



variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun _x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
 intro h h'
 intro x y xr yt
 intro y yt


variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) : Prop :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
 simp only [SetUb] at *
 intro x xs


open Function
example (c : ℝ) : Injective fun x ↦ x + c := by
 intro x xr
 dsimp
 intro h
 linarith

--  # The method used in the book
example (c : ℝ) : Injective fun x ↦ x + c := by
 intro x₁ x₂ h'
 exact (add_left_inj c).mp h'


example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
 intro x y
 dsimp
 intro h'
 rw [← one_mul x]
 nth_rewrite 1 [← inv_mul_cancel c]

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- # The composition of injective functions is injective

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
 intro x y
 dsimp
 intro h
 simp only [Injective] at *
 apply injg at h
 apply injf at h
 exact h
