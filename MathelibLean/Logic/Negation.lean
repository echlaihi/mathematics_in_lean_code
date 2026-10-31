import Mathlib

example {a b : ℝ} (h : a < b) : ¬ b < a := by
 intro h'
 have : a < a := lt_trans h h'
 apply lt_irrefl a this


def FnHasUb (f : ℝ → ℝ) :=
 ∃ a, ∀ x, f x ≤ a

def FnHasLb (f : ℝ → ℝ) :=
 ∃ a, ∀ x, a ≤ f x

example {f : ℝ → ℝ} (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
 intro fnub
--  simp only [FnHasUb] at h'
 rcases fnub with ⟨a,fnuba⟩
 rcases h a with ⟨x, hx⟩
 have : f x ≤  a := fnuba x
 linarith

example {f : ℝ → ℝ} (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
 intro fnlb
 rcases fnlb with ⟨a, fnlba⟩
 rcases h a with ⟨x, hx⟩
 have : a ≤ f x := fnlba x
 linarith

example : ¬FnHasUb fun x ↦ x := by
  intro fnub
  simp only [FnHasUb] at *
  rcases fnub with ⟨a, fnuba⟩
  have : a + 1 ≤ a := by
   apply fnuba
  linarith

#check not_le_of_gt
#check not_lt_of_ge
#check lt_of_not_ge
#check le_of_not_gt

example {a b : ℝ} {f : ℝ → ℝ} (h : Monotone f) (h' : f a < f b) : a < b := by
 simp only [Monotone] at h
--  apply h at


example {a b : ℝ} {f : ℝ → ℝ} (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
--  simp only [Monotone]
 intro h₂
 have : f a ≤ f b := by
  apply h₂
  exact h
 linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
 intro h
 let f := fun x : ℝ ↦ (0 : ℝ)
 have monof : Monotone f := by
  intro x y hxy
  apply
 have h' : f 1 ≤ f 0 := le_refl _
 sorry


-- example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
--  apply le_of_not_gt
--  intro h
--  have :


variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
 sorry

example (h : ∀ x, ¬P x) : ¬ ∃x, P x := by
 intro h
 rcases h with ⟨x, hx⟩
 have : ¬P x := by
  apply h

example (h : ¬∀ x, P x) : ∃ x,  ¬P x := by
 by_contra h'
 apply h
 intro x
 show P x
 by_contra h''
 exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
 sorry

example (h : ¬¬Q) : Q := by
 by_contra
 apply h
 exact this

example (h : Q) : ¬¬ Q := by
 by_contra
 apply this
 exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
 intro a
 simp only [FnHasUb] at h
 by_contra
 apply this

-- # The tactic `push_neg` or `push Not`
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
 push Not at h
 exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
 simp only [FnHasUb] at h
 push Not at h
 exact h

-- example {x y : ℝ}(h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y ≤ f x := by


-- # The` conrapose!` tactic
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
 simp only [FnHasUb] at h
 contrapose!  h
 exact h

example (x : ℝ)  (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
 contrapose! h
 use x/2
 constructor <;> linarith

-- # In case of proof by contradiction we use the following principle
-- # exfalso

example (h : 0 < 0) : a > 37 := by
 exfalso
 apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
 absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
 have h' : ¬0 < 0 :=  lt_irrefl 0
 contradiction
--  # linarith here also closes the goal
