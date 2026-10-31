import Mathlib

-- # To prove a statement in the form A ∧ B we split
-- # our proof into two cases using constructor tactic,
-- # the assumption tactic tells lean to search for a hypothesis that proves the goal
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
 constructor
 · assumption
 intro h
 apply h₁
 rw [h]

-- # This is the slick proof-term
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
 ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
 have h : x ≠ y := by
  contrapose! h₁
  rw [h₁]
 ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
 rcases h with ⟨h₀, h₁⟩
 contrapose! h₁
 exact le_antisymm h₀ h₁

-- # rintro tactic combine `rcases` and `intro`
example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
 rintro ⟨h₀, h₁⟩ h'
 exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
 fun  ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
 have ⟨h₀, h₁⟩ := h
 contrapose! h₁
 exact le_antisymm h₀ h₁

-- # all the tree next aproaches follows the pattern-matching syntax
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
 cases h
 case intro h₀ h₁ =>
   contrapose! h₁
   exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
 cases h
 next h₀ h₁ =>
   contrapose! h₁
   exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
 match h with
   | ⟨h₀, h₁⟩ =>
     contrapose! h₁
     exact le_antisymm h₀ h₁

-- # If we have a hypothesis with two components we can extract each one by h.left or h.right
-- # or equivalently h.1 and h.2

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
 intro h'
 apply h.right
 exact le_antisymm h.left h'

-- # Let's prove the following in verious ways
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : (m ∣ n) ∧ (¬n ∣ m) := by
 rcases h with ⟨h₀, h₁⟩
 constructor
 · exact h₀
 intro h'
 contrapose h₁
 push Not at h₁
 apply dvd_antisymm h₀ h'

-- # Let's prove it in a different way
example {m n : ℕ} (h : m ∣ n ∧ n ≠ m) : (m ∣ n) ∧ (¬ n ∣ m) := by
 have ⟨h₀, h₁⟩ := h
 constructor
 · assumption
 contrapose h₁
 apply dvd_antisymm h₁ h₀

-- # Another different approach
example {m n : ℕ} (h : m ∣ n ∧ n ≠ m) : (m ∣ n) ∧ (¬n ∣ m) := by
 sorry


theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 := by
 have h' : x^2 = 0 := by



example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 := by
 sorry


example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
 rw [abs_lt]
 intro h
 rcases h with ⟨h1, h2⟩
 constructor
 · linarith
 · linarith

-- # The proof in the book
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
 rw [abs_lt]
 intro h
 constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor
  · norm_num
  norm_num

-- # The proof in the book
example : 3 ∣ Nat.gcd 6 15 := by
 rw [Nat.dvd_gcd_iff]
 constructor <;> norm_num

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  simp only [Monotone]
  constructor
  · intro h₀
    push Not at h₀
    apply h₀
  intro h₁
  push Not
  apply h₁

-- # Let's try a different aproach
theorem not_monotone_iff' {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
 rw [Monotone]
 push Not
 rfl

example : ¬ Monotone fun x : ℝ ↦ -x := by
 rw [Monotone]
 push Not
 use 1, 3
 norm_num

-- # partialOrder is a binary relation that is transitive, reflexive, and antisymmetric
-- # preorder is a binary relation that is reflexive and and transitive
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
 rw [lt_iff_le_and_ne]

-- # this is how the previous example proved in the book
example : a < b ↔ a ≤ b ∧ a ≠ b := by
--  rw [lt_iff_le_not_le]

variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
 sorry

example {a b c : ℝ} : a < b → b < c → a < c := by
 intro h h'
 linarith
