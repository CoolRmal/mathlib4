import Mathlib.Tactic.Linter.IfThenElse

/-! Tests for the `ifThenElse` linter. -/

-- The tactic `if` is replaced by the corresponding `by_cases` proof.
/--
warning: Try this: ⏎
  i̵f̵ ̵h̵ ̵:̵ ̲ ̲b̲y̲_̲c̲a̲s̲e̲s̲ P
  ̲  ̲ ̲ ̲t̵h̵e̵n̵·̲ exact Or.inl h
      e̵l̵s̵e̵·̲ exact Or.inr h

Note: This linter can be disabled with `set_option linter.style.ifThenElse false`
-/
#guard_msgs in
example (P : Prop) : P ∨ ¬P := by
  if h : P then
    exact Or.inl h
  else
    exact Or.inr h

-- The non-dependent tactic `if` is flagged as well.
/--
warning: Try this: ⏎
  i̵f̵ ̲ ̲b̲y̲_̲c̲a̲s̲e̲s̲ P
  ̲  ̲ ̲ ̲t̵h̵e̵n̵·̲ exact 1
      e̵l̵s̵e̵·̲ exact 2

Note: This linter can be disabled with `set_option linter.style.ifThenElse false`
-/
#guard_msgs in
example (P : Prop) [Decidable P] : Nat := by
  if P then
    exact 1
  else
    exact 2

-- A branch that is a `_` or `?_` hole cannot be turned into a `by_cases` proof:
-- the linter falls back to a plain warning.
/--
warning: Please use `by_cases` instead of tactic-mode `if`.

Note: This linter can be disabled with `set_option linter.style.ifThenElse false`
-/
#guard_msgs in
example (P : Prop) : True := by
  if h : P then
    _
  else
    trivial
  all_goals trivial

-- Nested tactic `if`s are each flagged.
/--
warning: Try this: ⏎
  i̵f̵ ̵h̵P̵ ̵:̵ ̲ ̲b̲y̲_̲c̲a̲s̲e̲s̲ P
  ̲  ̲ ̲ ̲t̵h̵e̵n̵·̲ if hQ : Q then trivial else trivial
      e̵l̵s̵e̵·̲ trivial

Note: This linter can be disabled with `set_option linter.style.ifThenElse false`
---
warning: Try this: ⏎
  i̵f̵ ̵h̵Q̵ ̵:̵ ̲ ̲b̲y̲_̲c̲a̲s̲e̲s̲ Q
  ̲  ̲ ̲ ̲ ̲ ̲t̵h̵e̵n̵·̲ trivial
        e̵l̵s̵e̵·̲ trivial

Note: This linter can be disabled with `set_option linter.style.ifThenElse false`
-/
#guard_msgs in
example (P Q : Prop) : True := by
  if hP : P then
    if hQ : Q then
      trivial
    else
      trivial
  else
    trivial

-- The term-level `if` is not flagged.
#guard_msgs in
def foo (P : Prop) [Decidable P] : Nat := if P then 1 else 2

-- Neither is `by_cases`.
#guard_msgs in
example (P : Prop) : P ∨ ¬P := by
  by_cases h : P
  · exact Or.inl h
  · exact Or.inr h

-- A deactivated linter does nothing.
#guard_msgs in
set_option linter.style.ifThenElse false in
example (P : Prop) : P ∨ ¬P := by
  if h : P then
    exact Or.inl h
  else
    exact Or.inr h
