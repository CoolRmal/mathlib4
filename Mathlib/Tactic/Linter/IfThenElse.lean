/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public meta import Lean.Meta.Hint
public meta import Lean.Elab.Command
public meta import Mathlib.Lean.Linter
public import Lean.Meta.TryThis
public import Mathlib.Init

/-!
# The `ifThenElse` linter

The `ifThenElse` linter flags uses of the tactic `if ... then ... else ...` and suggests `by_cases`
tactic instead.
-/

meta section

open Lean Elab Linter Parser.Tactic

namespace Mathlib.Linter.IfThenElse

/-- The `ifThenElse` linter flags uses of the tactic `if ... then ... else ...` and suggests
the `by_cases` tactic instead. -/
public register_option linter.style.ifThenElse : Bool := {
  defValue := true
  descr := "enable the `ifThenElse` linter"
}

/-- `isTacticIf stx` checks whether `stx` is tactic-mode `if`, with or without
an explicitly named case hypothesis. -/
def isTacticIf (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Tactic.tacIfThenElse ||
    stx.isOfKind ``Lean.Parser.Tactic.tacDepIfThenElse

/-- Extract a genuine tactic sequence from an `if` branch.
Returns `none` for the special `_` and `?_` branches. -/
def getTacticSeq? (stx : Syntax) : Option (TSyntax ``Parser.Tactic.tacticSeq) :=
  if stx.isOfKind ``Parser.Tactic.tacticSeq then
    -- The trailing whitespace and comments of a branch belong to the surrounding source, not
    -- to the branch: without `unsetTrailing`, a trailing comment ends up inside the suggestion.
    some ⟨stx.unsetTrailing⟩
  else
    none

/-- Suggest the corresponding `by_cases` proof for one tactic-mode `if`. -/
def mkByCases? (stx : Syntax) :
    CoreM (Option (TSyntax ``Parser.Tactic.tacticSeq)) := do
  match stx with
  | `(tactic| if $h : $p then $pos else $neg) =>
      let some pos := getTacticSeq? pos | return none
      let some neg := getTacticSeq? neg | return none

      if h.raw.isIdent then
        let h : Ident := ⟨h.raw⟩
        some <$> `(tacticSeq|
          by_cases $h : $p
          · $pos
          · $neg)
      else
        -- Handles `if _ : P then ... else ...`
        some <$> `(tacticSeq|
          by_cases $p
          · $pos
          · $neg)

  | `(tactic| if $p then $pos else $neg) =>
      let some pos := getTacticSeq? pos | return none
      let some neg := getTacticSeq? neg | return none

      some <$> `(tacticSeq|
        by_cases $p
        · $pos
        · $neg)

  | _ =>
      return none

def ifThenElseLinter : Linter where
  run := whenLinterActivated linter.style.ifThenElse fun stx => do
    for s in stx.topDown do
      if isTacticIf s then
        match ← Command.liftCoreM <| mkByCases? s with
        | none =>
            logLint linter.style.ifThenElse s
              "Please use `by_cases` instead of tactic-mode `if`."
        | some replacement =>
            let suggs ← Command.liftCoreM <|
              Meta.Hint.mkSuggestionsMessage
                #[{
                  toTryThisSuggestion := replacement
                  span? := some s
                }]
                s none false

            logLint linter.style.ifThenElse s
              m!"Try this: {suggs}"

initialize addLinter ifThenElseLinter

end Mathlib.Linter.IfThenElse
