import Lean
import Qq

open Lean Elab Tactic Meta Lean.Meta.Tactic.TryThis
open Qq

syntax (name := endSorry) "sorry?" : tactic

set_option pp.all true

def letters := #["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z" ]

def getName (n : Nat) : Nat × String :=
  let base := letters[n % letters.size]!
  let rest := n / letters.size

  if rest > 0 then
    (n+1, s!"{base}{rest}")
  else
    (n+1, base)

set_option autoImplicit false

partial def loop (n := 0) : TacticM (String)  :=
    withMainContext do

      try
        let goal ← getMainGoal

        let type ← goal.getType

        match ← inferTypeQ type with
        | ⟨1, ~q(Prop), ~q($a = $b) ⟩ =>
          if ← isDefEq a b then
            goal.refl
            return "rfl"
          else
            admitGoal goal
            return "sorry"
        | ⟨1, ~q(Prop), ~q(True) ⟩ =>
          let intro := (.const `True.intro [])
          let goals ← goal.apply intro
          replaceMainGoal goals
          return "apply True.intro"
        | ⟨1, ~q(Prop), ~q((_ : ($a : Prop)) → ($b : Prop))⟩ =>
          let (n, name) := getName n
          let (_v, newGoal) ← goal.intro name.toName
          replaceMainGoal [newGoal]
          return s!"intro {name}\n{← loop n}"
        | ⟨1, ~q(Prop), ~q((_ : ($a : Type)) → ($b : Prop))⟩ =>
          let (n, name) := getName n
          let (_v, newGoal) ← goal.intro name.toName
          replaceMainGoal [newGoal]
          return s!"intro {name}\n{← loop n}"
        | ⟨2, ~q(Type), ~q((_ : ($a : Type)) → ($b : Type))⟩ =>
          let (n, name) := getName n
          let (_v, newGoal) ← goal.intro name.toName
          replaceMainGoal [newGoal]
          return s!"intro {name}\n{← loop n}"
        | ⟨1, ~q(Prop), ~q(¬$a) ⟩ =>
          let (n, name) := getName n
          let (_v, newGoal) ← goal.intro name.toName
          replaceMainGoal [newGoal]
          return s!"intro {name}\n{← loop n}"
        | ⟨1, ~q(Prop), a⟩ =>
          let ctx ← getLCtx
          let option_matching_expression ← ctx.findDeclM? fun decl => do
            let declExpr := decl.toExpr
            let declType ← inferType declExpr
            if ← isDefEq declType type
              then return some (declExpr, decl.userName)
              else return none
          match option_matching_expression with
          | none =>
            Lean.logInfo s!"By default: {a}"
            admitGoal goal
            return "sorry"
          | some (e, userName) =>
            closeMainGoal `endSorry e
            return s!"exact {userName}"
      catch _e =>
        return ""

elab_rules : tactic
  | `(tactic| sorry?) => do
    let ref ← getRef
    let raw ← loop

    let text := SuggestionText.string raw
    let suggestion : Suggestion := {suggestion := text}

    addSuggestion ref suggestion

    return
