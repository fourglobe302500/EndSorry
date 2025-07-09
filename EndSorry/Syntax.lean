import Lean
import Qq

open Lean Elab Tactic Meta Lean.Meta.Tactic.TryThis
open Qq

syntax (name := endSorry) "sorry?" : tactic

set_option pp.all true

elab_rules : tactic
  | `(tactic| sorry?) =>
    withMainContext do
      let goal ← getMainGoal
      let type ← goal.getType
      let ref ← getRef

      match ← inferTypeQ type with
      | ⟨1, ~q(Prop), ~q($a = $b)⟩ =>
        Lean.logInfo s!"By Eq: {a}"
        Lean.logInfo s!"By Eq: {b}"
        if ← isDefEq a b then
          goal.refl
          addTermSuggestion ref (.const `rfl [])
        else
          return ← admitGoal goal
      | ⟨_u, _α, a⟩ =>
        Lean.logInfo s!"By default: {a}"
        addTermSuggestion ref (.const `sorry [])
        admitGoal goal
