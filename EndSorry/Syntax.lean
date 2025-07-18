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

def Lean.Expr.matchArrow? (e : Expr): Option (Expr × Expr) :=
  match e with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then none
    else (a, b)
  | _ => none

def finished : TacticM Bool := do
  return (← getUnsolvedGoals).length == 0

def Lean.LocalContext.firstMapM? [Monad m] (lctx: LocalContext) (f : LocalDecl → m (Option α)) : m (Option α) :=
  lctx.foldlM (init := none) fun acc decl => match acc with
    | some _ => return acc
    | none => f decl

def handleDefault (goal : MVarId) (n : Nat) : TacticM (String × Nat) := do
  let type ← goal.getType
  let ctx ← getLCtx
  let option_matching_expression ← ctx.findDeclM? fun decl => do
    if decl.isImplementationDetail then return none
    else
      let declExpr := decl.toExpr
      let declType ← inferType declExpr
      if ← isDefEq declType type
        then return some (declExpr, decl.userName)
        else return none
  if let some (e, userName) := option_matching_expression then
    closeMainGoal `endSorry e
    -- logInfo m!"exact {userName}"
    return (s!"exact {userName}", n)

  if let some (_a, _b) := type.matchArrow? then
    let (n, name) := getName n
    let (_v, newGoal) ← goal.intro name.toName
    replaceMainGoal [newGoal]
    -- logInfo m!"intro {name}"
    return (s!"intro {name}", n)
  else if type.isForall then
    let (res, n) ← forallBoundedTelescope type (some 1) (fun _fvars _body => do
      let (n, name) := getName n
      let (_v, newGoal) ← goal.intro name.toName
      replaceMainGoal [newGoal]
      -- logInfo m!"intro {name}"
      return (s!"intro {name}", n))
    return (res, n)
  else if let some (_, p) := type.app2? ``Exists then
    let res ← lambdaBoundedTelescope p 1 (fun _fvars _body => do
      let newGoals ← goal.constructor
      replaceMainGoal newGoals
      -- logInfo m!"constructor"
      return s!"constructor")
    return (res, n)

  let result ← ctx.firstMapM? (fun decl => do
    if decl.isImplementationDetail then return none
    let declExpr := decl.toExpr
    let declName := decl.userName
    match ← inferTypeQ declExpr with
    | ⟨0, ~q($a ∧ $b), declq⟩ =>
      let (n, na) := getName n
      let ea : Expr := q(And.left $declq)
      let (n, nb) := getName n
      let eb : Expr := q(And.right $declq)
      let (_vars, goal) ←
        goal.assertHypotheses #[
          { userName := na.toName, type := ← inferType ea, value := ea },
          { userName := nb.toName, type := ← inferType eb, value := eb }]
      let goal ← goal.clear decl.fvarId
      replaceMainGoal [goal]
      -- logInfo m!"rcases {declName} with ⟨{na}, {nb}⟩"
      return some (s!"rcases {declName} with ⟨{na}, {nb}⟩", n)
    | _ => return none)


  if let some (s, n) := result then
    return (s, n)
  else
    -- Lean.logInfo m!"By default: {type}"
    admitGoal goal
    return (s!"sorry", n)

def process (goal : MVarId) (n : Nat) : TacticM (String × Nat) := do
  let type ← goal.getType
  match ← inferTypeQ type with
  | ⟨1, ~q(Prop), ~q($a = $b) ⟩ =>
    if ← isDefEq a b then
      goal.refl
      return ("rfl", n)
    else
      admitGoal goal
      return ("sorry", n)
  | ⟨1, ~q(Prop), ~q($a ∧ $b) ⟩ =>
    let newGoals ← goal.constructor
    replaceMainGoal newGoals
    -- logInfo m!"constructor"
    return ("constructor", n)
  | ⟨1, ~q(Prop), ~q(True) ⟩ =>
    let intro := (.const `True.intro [])
    let goals ← goal.apply intro
    replaceMainGoal goals
    return ("apply True.intro", n)
  | ⟨1, ~q(Prop), ~q(¬$a) ⟩ =>
    let (n, name) := getName n
    let (_v, newGoal) ← goal.intro name.toName
    replaceMainGoal [newGoal]
    -- logInfo m!"intro {name}"
    return (s!"intro {name}", n)
  | ⟨1, ~q(Prop), ~q($a ∨ $b) ⟩ =>
    -- logInfo m!"Or"
    let newGoals ← goal.constructor
    replaceMainGoal newGoals
    -- logInfo m!"constructor"
    return ("constructor", n)
  | ⟨1, ~q(Prop), _a⟩ =>
    handleDefault goal n

partial def loop (n := 0) : TacticM (String)  :=
    withMainContext do
      let goal ← getMainGoal

      let (text, n) ← process goal n
      if ← finished then
        return text
      else
        let raw ← loop n
        return s!"{text}\n{raw}"

elab_rules : tactic
  | `(tactic| sorry?) => do
    let ref ← getRef
    let raw ← loop

    let text := SuggestionText.string raw
    let suggestion : Suggestion := {suggestion := text}

    addSuggestion ref suggestion

    return
