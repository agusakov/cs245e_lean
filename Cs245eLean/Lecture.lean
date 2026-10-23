variable (p q : Prop)

variable (p q : Prop)
variable (hpq : p → q) (hp : p)
#check (hpq hp)

/- **Modus Ponens** -/
theorem modus_ponens (hpq : p → q) (hp : p) : q := by
  apply hpq
  exact hp

/- **Commutativity of Conjunction** -/
theorem and_comm' (hpq : p ∧ q) : q ∧ p := by
  refine ⟨?_, ?_⟩
  · exact hpq.right
  · exact hpq.left

/- **Contrapositive** -/
theorem contrapositive (hab : p → q) : ¬ q → ¬ p := by
  intros hb ha
  apply hb
  apply hab
  apply ha
