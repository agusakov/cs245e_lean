import Mathlib.Tactic.ByContra

/- **Negation**
 Lean uses intuitionistic logic, which means the way negation works is
  different from our formal deduction system. You can think of
  `¬A` as being equivalent to `A → False`.

  The closest analogue in Lean to `(¬-)` and `(¬+)` is `by_contra`, which still
  assumes the negation of the conclusion, but replaces the goal with
  `False` instead of asking for an explicit formula to contradict with itself.

  *Caution*: This does not mean you can use `False` in our regular formal
  deduction proofs in class, as that is a different deduction system where
  `False` does not exist as a formula. -/

variable {A B C D : Prop}

/- **Examples** -/
theorem contrapositive (hab : A → B) : ¬ B → ¬ A := by
  intros hb ha
  apply hb
  apply hab
  apply ha

example (hab : A → B) : ¬A ∨ B := by
  by_contra hnab
  · apply contrapositive hab
    · by_contra hb -- Behaves similar to `(¬+)`, but changes the goal to `False`.
      apply hnab
      right
      exact hb
    · by_contra ha -- Behaves similar to `(¬-)`, but changes the goal to `False`.
      apply hnab
      left
      exact ha

/- **Exercises** -/
theorem double_neg : ¬¬ A → A := by
  sorry

example (hab : ¬A ∨ B) : A → B := by
  sorry

-- challenge question (you can use previous theorems)
example (hac : A → C) (hnac : ¬ A → C) : C := by
  sorry
