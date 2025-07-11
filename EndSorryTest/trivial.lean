import EndSorry

-- set_option pp.all true
set_option autoImplicit false

theorem reflection {α : Type} (a : α) : a = a := by
  -- rfl
  sorry?

theorem true : True := by
  -- apply True.intro
  sorry?

theorem false : ¬False := by
  -- intro a
  -- exact a
  sorry?

theorem a_true {α : Type} : α → True := by
  -- intro a
  -- apply True.intro
  sorry?

theorem a_then_a {α : Prop} : α → α := by
  -- intro a
  -- exact a
  sorry?

theorem a_b_true {α β : Type} : α → β → True := by
  -- intro a
  -- intro b
  -- apply True.intro
  sorry?

theorem a_b_then_a {β : Type} {α : Prop} : α → β → α := by
  -- intro a
  -- intro b
  -- exact a
  sorry?

theorem a_b_then_b {α : Type} {β : Prop} : α → β → β := by
  -- intro a
  -- intro b
  -- exact b
  sorry?

theorem a_a : ∃ α, α  → True := by
  sorry?

theorem a_b : ∀ α, α  → True := by
  sorry?
