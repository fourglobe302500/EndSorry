import EndSorry

-- set_option pp.all true
-- set_option autoImplicit true

set_option pp.raw true
set_option pp.raw.maxDepth 10

theorem reflection {α : Type} (a : α) : a = a := by
  rfl
  -- sorry?

theorem true : True := by
  apply True.intro
  -- sorry?

theorem false : ¬False := by
  intro a
  exact a
  -- sorry?

theorem a_true {α : Type} : α → True := by
  intro a
  apply True.intro
  -- sorry?

theorem a_then_a {α : Prop} : α → α := by
  intro a
  exact a
  -- sorry?

theorem direct {α : Prop} (h : α) : α := by
  exact h
  -- sorry?

theorem a_b_true {α β : Type} : α → β → True := by
  intro a
  intro b
  apply True.intro
  -- sorry?

theorem a_b_then_a {α : Prop} : α → β → α := by
  intro a
  intro b
  exact a
  -- sorry?

theorem a_b_then_b {β : Prop} : α → β → β := by
  intro a
  intro b
  exact b
  -- sorry?

theorem test : ∃ n : Nat, n = 0 := by
  constructor
  rfl
  -- sorry?

theorem a_b : ∀ α, α  → True := by
  intro α
  intro b
  apply True.intro
  -- sorry?

theorem a_and_b : a → b → a ∧ b := by
  intro a
  intro b
  constructor
  exact a
  exact b
  -- sorry?

theorem a_and_b_given (ha : a) (hb: b) : a ∧ b := by
  constructor
  exact ha
  exact hb
  -- sorry?

theorem a_and_b_then_a {α β : Prop} : α ∧ β → α := by
  -- intro a
  -- rcases a with ⟨b, c⟩
  -- exact b
  sorry?

theorem a_and_b_and_c_then_c {α β χ : Prop} : α ∧ β ∧ χ → χ := by
  -- intro a
  -- rcases a with ⟨b, c⟩
  -- exact b
  sorry?
