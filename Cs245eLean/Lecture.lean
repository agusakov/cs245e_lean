variable (p q : Prop)

/- **Modus Ponens** -/
theorem modus_ponens (hpq : p → q) (hp : p) : q := by
  apply hpq -- This is like `(→-)`
  exact hp

/- **Commutativity of Conjunction** -/
theorem and_comm' (hpq : p ∧ q) : q ∧ p := by
  refine ⟨?_, ?_⟩ -- This is like `(∧+)`
  · apply hpq.right -- This is like `(∧-)`
  · apply hpq.left -- This is like `(∧-)`
