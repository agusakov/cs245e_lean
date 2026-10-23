import Mathlib.Tactic.ByContra

/- **Negation**
  Lean uses intuitionistic logic, which means the way negation works is
  different from our formal deduction system. In Lean, you can think of
  `¬A` as being equivalent to `A → False`.

  As a consequence, Lean doesn't really have an analogue to `(¬-)` and `(¬+)`.
  Instead, we have `by_contra`, which also assumes the negation of the conclusion,
  but replaces the goal with `False` instead of asking for explicit formulas `B` and `¬ B`.

  *Caution*: This does not mean you can use `False` in our regular formal
  deduction proofs in class, as that is a different deduction system where
  `False` does not exist as a formula.

  In this file, we'll also see that `apply` can be used with theorems, not just hypotheses. -/

variable {A B C D : Prop}

/- **Examples** -/
theorem contrapositive (hab : A → B) : ¬ B → ¬ A := by
  intros hb ha
  apply hb
  apply hab
  apply ha

example (hab : A → B) : ¬A ∨ B := by
  by_contra hnab -- Takes the negated conclusion as a hypothesis and changes the goal to `False`.
  apply contrapositive hab -- Use our previous lemma
  /- At this point, we have two goals: `¬ B` and `A`. -/
  · by_contra hb -- Takes the un-negated conclusion as premise `hb : B`
                  -- and changes the goal to `False`.
    apply hnab
    right
    exact hb
  · by_contra ha -- Takes the negated conclusion as premise `ha : A`
                 -- and changes the goal to `False`.
    apply hnab
    left
    exact ha

/- **Practice** -/
theorem double_neg : ¬¬ A → A := by
  sorry

example (hab : ¬A ∨ B) : A → B := by
  sorry

-- challenge question (you can use previous theorems)
example (hac : A → C) (hnac : ¬ A → C) : C := by
  sorry
