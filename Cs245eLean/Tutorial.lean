import Mathlib.Tactic.ByContra

variable {A B C : Prop}

/- **Implication**
  Our implication tactics are pretty straightforward:

  `intros h` - we can use this when the goal is of the form `⊢ A → B`. The `intros`
    tactic is similar to `(→+)`, where we introduce `h : A` to our premise set
    and our goal becomes `⊢ B`.
  `apply h` - if we have a hypothesis `h : A → B` and goal  `⊢ B`, we can use
    this tactic to change our goal to `⊢ A`. This tactic is similar to `(→-)`.
  `exact h` - if we have hypothesis `h : A` that matches our goal `⊢ A`, we can use
    `exact` to close the goal.
 -/

example (hAB : A → B) (hA : A) : B := by
  apply hAB
  exact hA

theorem hypothetical_syllogism (h1 : A → B) (h2 : B → C) : A → C := by
  intros ha
  apply h2
  apply h1
  exact ha

/- **Conjunction**

  For conjunction, we have the following tactics:
  `refine ⟨?_, ?_⟩` - this takes a goal of the form `⊢ A ∧ B` and breaks it up into two
    separate goals, `⊢ A` and `⊢ B`. We denote the subgoals by using `·` in front of them
    and indenting them (Lean is whitespace sensitive). This is similar to our `(∧+)` tactic.
      * Note: The angle brackets `⟨ ⟩` are constructors for a conjunction, so
        if we had premises `ha : A` and `hb : B`, we could inline our proof as
        `refine ⟨ha, hb⟩`. We use `?_` to tell Lean to create subgoals.
  `h.left` and `h.right` - this isn't a tactic, but we can use it with other tactics. If
    we have premise `h : A ∧ B`, then `h.left` or `h.1` gives us `A`, and `h.right` or
    `h.2` gives us `B`. This is similar to our `(∧-)` tactic, though note that here
    it works on premises.
  -/

example : A ∧ B → A := by
  intros hab
  exact hab.1

/- Commutativity of `and` -/
example (hab : A ∧ B) : B ∧ A := by
  refine ⟨?_, ?_⟩
  · exact hab.2
  · exact hab.1

-- Try solving this in term mode.
example (hab : A ∧ B) : B ∧ A := ⟨hab.2, hab.1⟩

/- **Disjunction**

  For disjunction, we have the following tactics:
  `obtain ha | hb := hab` - This takes in a premise `hab : A ∨ B` and breaks it up into new
    premises `ha : A` and `hb : B`. This is similar to our `(∨-)` proof rule.
  `left` and `right` - This works on a goal of the form `⊢ A ∨ B` and replaces it with either
    `⊢ A` or `⊢ B` respectively. This is similar to our `(∨+)` proof rule.
   -/

/- Commutativity of `or` -/
example (hab : A ∨ B) : B ∨ A := by
  obtain ha | hb := hab
  · right
    exact ha
  · left
    exact hb

example : A → A ∨ B := by
  intros ha
  left
  exact ha

example (ha : A) : A ∨ (A ∧ B) := by
  left
  exact ha

example (habc : A ∨ (A ∧ B)) : A := by
  obtain ha | hab := habc
  · exact ha
  · exact hab.1

/- **Negation**
  Lean uses intuitionistic logic, which means the way negation works is
  different from our formal deduction system. In Lean, you can think of
  `¬A` as being equivalent to `A → False`.

  As a consequence, Lean doesn't really have an analogue to `(¬-)` and `(¬+)`.
  Instead, we have `by_contra`, which also assumes the negation of the conclusion,
  but replaces the goal with `False` instead of asking for explicit formulas `B` and `¬ B`.
  Note - it is not a tactic that you have access to by default in Lean, you have to
  actually import it! We actually import it at the top of this file.

  *Caution*: This does not mean you can use `False` in our regular formal
  deduction proofs in class, as that is a different deduction system where
  `False` does not exist as a formula.

  In this file, we'll also see that `apply` can be used with theorems, not just hypotheses. -/

theorem contrapositive (hab : A → B) : ¬B → ¬A := by
  intros hnb ha
  apply hnb
  apply hab
  exact ha

theorem double_neg : ¬¬ A → A := by
  intros hnna
  by_contra hna
  apply hnna
  exact hna

example (hab : A → B) : ¬A ∨ B := by
  by_contra hab2
  have hab3 := contrapositive hab
  apply hab3
  · by_contra hb
    apply hab2
    right
    exact hb
  · by_contra hna
    apply hab2
    left
    exact hna


/- We can use this theorem to simulate our CS245 formal deduction system. -/
theorem non_contradiction (A) : A ∧ ¬ A → False := by
  intros haa
  apply haa.2
  exact haa.1

/- Challenge questions: Try first writing the proof in our formal deduction system,
  then using `non_contradiction` to prove them using a similar approach. -/
example (hab : ¬(A ∨ B)) : ¬A ∧ ¬B := by
  by_contra hab2
  apply non_contradiction A
  refine ⟨?_, ?_⟩
  · by_contra ha
    apply non_contradiction (¬A ∧ ¬B)
    refine ⟨?_, ?_⟩
    · refine ⟨ha, ?_⟩
      by_contra hb
      apply non_contradiction (A ∨ B)
      refine ⟨?_, hab⟩
      right
      exact hb
    · exact hab2
  · by_contra ha
    apply non_contradiction (A ∨ B)
    refine ⟨?_, hab⟩
    · left
      exact ha

-- For this one, you will need to think about what formula to plug into `non_contradiction`.
example (hac : A → C) (hnac : ¬ A → C) : C := by
  by_contra hnc
  apply non_contradiction A
  refine ⟨?_, ?_⟩
  · by_contra hna
    apply non_contradiction C
    refine ⟨hnac hna, hnc⟩
  · by_contra ha
    apply non_contradiction C
    refine ⟨hac ha, hnc⟩

example : A ∨ ¬ A := by
  by_contra haa
  apply non_contradiction A
  refine ⟨?_, ?_⟩
  · by_contra ha
    apply haa
    right
    exact ha
  · by_contra hna
    apply haa
    left
    exact hna
