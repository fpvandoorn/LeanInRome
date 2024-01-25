import Mathlib
import ProofWidgets.Demos.Rubiks
import LeanInRome.Common
open ProofWidgets.Jsx Real MeasureTheory
open Lean Meta Elab Tactic Complex
set_option linter.unusedVariables false







#check 3
#check (3 : ℝ)
#check π
#check I
#check (Real.sin)
#check ℝ
#check Type 0
#check Type 1

variable (x : ℝ) (s : ℕ)

#check x ∈ s
















/-
theorem add_comm {G : Type*} [AddCommMagma G]
  (a : G) (b : G) :
  a + b = b + a
-/

example (a b c : ℝ) : a * b + c = c + a * b := by
  exact add_comm (a * b) c

/-
* Lean figures out that (G := ℝ) from context
  (by looking at the type of a, b, c)
* Lean has a database of types where addition commutes,
  and looks up to see that it is true for ℝ
(*type-class inference*) -/



example (a b c : ℝ) : a * b + c = c + a * b := by
  exact add_comm (G := ℝ) (a * b) c

example (a b c : ℝ) : a * b + c = c + a * b := by
  exact add_comm _ _

example (a b c : ℝ) : a * b + c = c + a * b := by
  apply add_comm
















/- `#print` prints the full proof of a theorem,
but in an unreadable internal representation -/

#print integral_sin












set_option pp.all true in
#print integral_sin















#print axioms integral_sin

variable {f : ℝ → ℝ} {x : ℝ}

#check f x
#reduce (fun a ↦ f a) x -- β-reduction

example : (fun a ↦ f a) x = f x := by
  rfl

example : (fun a ↦ f a) =
    (fun b ↦ f b) := by
  rfl -- α

example : (fun a ↦ f a) =
    f := by
  rfl -- η




/- You can declare notation -/

notation3 "∫ "(...)" in "a".."b",
  "r:60:(scoped f => intervalIntegral f a b volume) => r



/- You can declare your own tactics -/

elab "my_assumption" : tactic => do
  let target ← getMainTarget
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if ← isDefEq ldecl.type target then
      closeMainGoal ldecl.toExpr
      return
  throwTacticEx `my_assumption (← getMainGoal)
    m!"no matching hypothesis of type {indentExpr target}"


example (n m : ℕ) (h1 : 0 ≤ m) (h2 : n = 0) (h3 : m ≤ 9) : n = 0 := by
  my_assumption



/- You can declare widget -/


def eg2 := #["L", "L", "D⁻¹", "U⁻¹", "L", "D", "D", "L", "U⁻¹", "R", "D", "F", "F", "D"]

#html <Rubiks seq={eg} />



example (x : ℝ) : rexp (2 * x) = rexp x * rexp x := by sorry











/-
You can even declare a small language,
and write a parser for that language.

In fact, almost every part of Lean
(parsing, elaboration, tactics, compilation)
are written *in Lean*
(the kernel is not written in Lean)
-/
