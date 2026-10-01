variable {A B C : Prop}

/-
*** Differences between our formal deduction system and Lean ***
  - Every premise has a label.
  - Lean uses intuitionistic logic
-/

/- Commutativity of `and` -/
example (hab : A ∧ B) : B ∧ A := by
  refine ⟨?_, ?_⟩ -- This is like (∧+)
  · apply hab.right -- This is like (∧-)
  · apply hab.left -- This is like (∧-)

/- Commutativity of `or` -/
example (hab : A ∨ B) : B ∨ A := by
  obtain ha | hb := hab -- This is like (∨-)
  · right -- This is like (∨+)
    apply ha
  · left -- This is like (∨+)
    apply hb


/- Fill in the following `sorry`s -/
example (ha : A) : A ∨ (A ∧ B) := by
  sorry

example (habc : A ∨ (A ∧ B)) : A := by
  sorry
