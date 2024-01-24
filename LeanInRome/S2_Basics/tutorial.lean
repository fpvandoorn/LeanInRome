import LeanInRome.Common
import Mathlib.Data.Real.Basic

/-
# Apply, rewrite, and linarith
-/

/-
## Checking types
-/

section

/-
Here, we introduce two real-number variables using `variable`.
`ℝ`  is typed as `\R`, followed by a space or tab character.
-/
variable (a b : ℝ)

/-
`#check` shows `a : ℝ`. That is, `a` is a real number variable.
-/

#check a

/-
In Lean, theorems are types.

Note `mul_comm a b` has type `a * b = a * b`. That is, `mul_comm a b` is a proof that
`a * b = b * a`.
-/

#check mul_comm a b

end

/-
## Rewriting

### Rewriting the target

In its most basic form, the `rw` tactic changes the target (that which is to be proved) and
closes the goal (completes the current proof or subproof), if possible.
-/

section section1

variable (u v w : ℝ)

/-
Here, the goal is to prove `u * (v * w) = u * (w * v)`.
Recall `mul_comm v w` is a proof of `v * w = w * v`.
The effect of `rw [mul_comm v w]` is to change every occurrence of `v * w` in the target with
`w * v`.
Here, the target changes to `u * (w * v) = u * (w * v)`. The `rw` tactic recognises that this is
true by definition of equality and closes the goal.
-/

example : u * (v * w) = u * (w * v) := by
  rw [mul_comm v w]

/-
### Associativity

The `mul_assoc` theorem proves `a * b * c = a * (b * c)`, for all `a`, `b` `c` of type `G`, where
`G` is a semigroup.

Note: multiplication in Lean is 'left associative'. This means `a * b * c = a * (b * c)` should be
interpreted as `(a * b) * c = a * (b * c)`.
-/

#check mul_assoc

/-
### Using `sorry` and working interactively
We'll construct the proof of `(u * v) * w = v * (u * w)` iteratively, starting with a `sorry`
'proof'. Here, `sorry` tells Lean to emit a warning rather than an error message. Effectively, it's
asking Lean not to worry that the proof is incomplete.
-/

example : (u * v) * w = v * (u * w) := by
  sorry

/-
Place the cursor just before the `sorry`. This shows the 'tactic state' in the Infoview window:

  u v w : ℝ
  ⊢ u * v * w = v * (u * w)

The target is `⊢ u * v * w = v * (u * w)`, to prove `u * v * w = v * (u * w)`.

Let's start by rewriting the target with `rw [mul_comm u v]`
-/

example : (u * v) * w = v * (u * w) := by
  rw [mul_comm u v]
  sorry

/-
The new target is to prove `v * u * w = v * (u * w)`. Note I keep the `sorry`.
-/

/-
We finish the proof with `rw [mul_assoc u v w]
-/

example : (u * v) * w = v * (u * w) := by
  rw [mul_comm u v]
  rw [mul_assoc v u w]

/-
### Partial application
-/

/-
`mul_comm u` is the theorem that for *every* real number `b`, `u * b = b * u`

This is a partial application of `mul_comm`. The `rw` tactic can work with partial applications.
Here is a more efficient proof of the result above.
-/

example : (u * v) * w = v * (u * w) := by
  rw [mul_comm u]
  rw [mul_assoc]

/-
What happens if you remvove `u` in `rw [mul_comm u]`?
-/

/-
### Using local hypotheses

`mul_comm` and `mul_assoc` are theorems proved in Mathlib. You can also use `rw` with hypothesis
local to the current theorem or proof.

Below, we introduce the hypothesis `u * v = w` and label this hypothesis `h`.
-/

example (h : u * v = w) : (u * v) * u = u * w := by
  rw [h]
  rw [mul_comm]

/-
Multiple rewrites can be expressed on one line, separating the hypotheses by commas.
-/

example (h : u * v = w) : (u * v) * u = u * w := by
  rw [h, mul_comm]

/-
### Reversing identities

What if we have the hypothesis `h : w * u = u * v` and wish to prove `(u * v) * w = u * (w * w)`.

What happens if we try `rw [h]`?

Instead we want to try rewriting with the equation `u * v = w * u`. This we do via `rw [←h]`.

The left arrow `←` is typed `\l`.
-/

example (h : w * u = u * v) : (u * v) * w = u * (w * w) := by
  rw [←h]
  sorry

example (h : w * u = u * v) : (u * v) * w = u * (w * w) := by
  rw [←h]
  rw [mul_comm w]
  rw [mul_assoc]

/-
### Rewriting at a hypothesis

As before, suppose we have the hypothesis `w * u = u * v`, labelled `h`. We wish to prove
`(v * u) * w = u * (w * w)`. We can't immediately use `h` or its reverse. We can use `mul_comm` on
the target or we can rewrite at the hypothesis.

Doing `rw [mul_comm u v] at h` replaces `h` with

`w * u = v * u`
-/

example (h : w * u = u * v) : (v * u) * w = u * (w * w) := by
  rw [mul_comm u v] at h
  sorry

example (h : w * u = u * v) : (v * u) * w = u * (w * w) := by
  rw [mul_comm u v] at h
  rw [←h]
  rw [mul_comm w]
  rw [mul_assoc]


/-
## Calculation proofs

We can write proofs in the style of a 'calculation'
-/

example (h : u * v = w) : (u * v) * u = u * w :=
  calc
    (u * v) * u  = sorry := by sorry
    _ = u * w := by sorry

example (h : u * v = w) : (u * v) * u = u * w :=
  calc
    (u * v) * u  = w * u := by
      rw [h]
    _ = u * w := by
      rw [mul_comm]

/-
## The ring tactic

`ring` proves many identities over rings
-/

example : (u + v) * (v + w) = u * (w + v) + (v + w) * v:= by
  ring

end section1

/-
## Proving identities with rewrite, have, and apply

Lean rings need not be commutative
-/

section section2

#check mul_zero

namespace MyRing
variable {R : Type*} [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

/-
### The 'have' tactic

The `have` tactic is used to make a claim. This introduces new goal.
Below, we claim `a * 0 + a * 0 = a * 0 + 0`. This is followed by a proof. We label the new
hypothesis `h` and then use this hypothesis in the final line.
-/

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]


/-
### The apply tactic

If the target matches the conclusion of a theorem, you can use `apply` either to close the goal
or to replace the target with the hypotheses of the used theorem.

In our use below, the target is to prove `-b = a`, matching the conclusion of
`neg_eq_of_add_eq_zero`

Using `apply neg_eq_of_add_eq_zero` replaces the target with one of proving `b + a = 0`.
-/
theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  symm
  show -b = a
  apply neg_eq_of_add_eq_zero
  rw [add_comm, h]

end MyRing

end section2

/-
## Using theorems and Lemmas

`rw` is sufficient for using results whose conclusion is an equation.
For more general theorems (such as those whose conclusions are inequalities), we can use `apply`.
-/

section section3

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

/-
Note that `le_trans` has two goals, so when we try `apply le_trans`, we need to
close two goals.

We indent the goals and use a `·` at the start of the new goal. Type `·` using `\.`.

Why do I have three goals below instead of two?
-/

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · sorry
  . sorry
  · sorry


example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

/-
### The linarith tactic

`linarith` is like `ring` but can be used to prove results in 'linear arithmetic', this includes
many inequalities.
-/

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  linarith

end section3
