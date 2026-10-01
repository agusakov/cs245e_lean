/- **Lean Proofs**
  The basic blocks of Lean proofs are called tactics. Tactics behave somewhat like our
  formal deduction rules, in that they manipulate either the premises or goal. However,
  there are a couple key differences:
  - Premises, or hypotheses, have names, e.g. `(h : A → B)`, where `h` is the
    name of the premise.
  - Instead of writing the set of premises in each line, Lean automatically updates
    them in the Infoview on the right. If you click around the lines of a proof,
    you should see the proof state change in the Infoview panel on the right.

  For each section, we include some examples of solved problems with some annotations,
  and a section of exercises which start out with placeholder `sorry` tactics (this just
  allows us to tell Lean not to give us errors). Your goal is to replace the `sorry`s with
  proofs in a way where Lean will not give you errors.

  Our limited tactic list for this assignment will be the following:
  `(→+)` : `intros`
  `(→-)` : `apply`
  `(∧+)` : `refine`
  `(∧-)` : `h.left` or `h.right` (or equivalently `h.1` or `h.2`)
  `(∨+)` : `left` or `right`
  `(∨-)` : `obtain` -/

variable {A B C D : Prop} -- this is a declaration that `A B C D` are all propositions.

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

/- **Examples** -/
example (hAB : A → B) (hA : A) : B := by
  apply hAB -- This is like `(→-)`
  exact hA

theorem hypothetical_syllogism (h1 : A → B) (h2 : B → C) : A → C := by
  intros hA -- This is like `(→+)`
  apply h2 -- `(→-)`
  apply h1 -- `(→-)`
  exact hA

/- **Exercises** -/
-- Note: This one only works in this direction!
example (h : (A → B) → C) : A → (B → C) := by
  sorry

/- **Conjunction**

  For conjunction, we have the following tactics:
  `refine ⟨?_, ?_⟩` - this takes a goal of the form `⊢ A ∧ B` and breaks it up into two
    separate goals, `⊢ A` and `⊢ B`. We denote the subgoals by using `·` in front of them
    and indenting them. This is similar to our `(∧+)` tactic.
      * Note: The angle brackets `⟨ ⟩` are constructors for a conjunction, so
        if we had premises `ha : A` and `hb : B`, we could inline our proof as
        `refine ⟨ha, hb⟩`. We use `?_` to tell Lean to create subgoals.
  `h.left` and `h.right` - this isn't a tactic, but we can use it with other tactics. If
    we have premise `h : A ∧ B`, then `h.left` or `h.1` gives us `A`, and `h.right` or
    `h.2` gives us `B`. This is similar to our `(∧-)` tactic, though note that here
    it works on premises.
  -/

/- **Examples** -/
example : A ∧ B → A := by
  intros hab
  exact hab.left

/- Commutativity of `and` -/
example (hab : A ∧ B) : B ∧ A := by
  refine ⟨?_, ?_⟩ -- This is like `(∧+)`
  · exact hab.right -- This is like `(∧-)`
  · exact hab.left -- This is like `(∧-)`

-- equivalently, can also inline the subgoals:
example (hab : A ∧ B) : B ∧ A := by
  refine ⟨hab.2, hab.1⟩

/- **Exercises** -/
example (h : A ∧ B → C) : A → B → C := by
  sorry

example (h : A → B → C) : A ∧ B → C := by
  sorry

example (h : A → B) : (A ∧ C) → (B ∧ C) := by
  sorry

example (h : (A → B) ∧ (C → D)) : (A ∧ C) → (B ∧ D) := by
  sorry


/- **Disjunction**

  For disjunction, we have the following tactics:
  `obtain ha | hb := hab` - This takes in a premise `hab : A ∨ B` and breaks it up into new
    premises `ha : A` and `hb : B`. This is similar to our `(∨-)` proof rule.
  `left` and `right` - This works on a goal of the form `⊢ A ∨ B` and replaces it with either
    `⊢ A` or `⊢ B` respectively. This is similar to our `(∨+)` proof rule.
   -/

/- **Examples** -/
/- Commutativity of `or`-/
example (hab : A ∨ B) : B ∨ A := by
  obtain ha | hb := hab -- This is like `(∨-)`
  · right -- This is like `(∨+)`
    apply ha
  · left -- This is like `(∨+)`
    apply hb

example : A → A ∨ B := by
  intros ha
  left
  apply ha

/- **Exercises** -/
example (h : A → B) : (A ∨ C) → (B ∨ C) := by
  sorry

example (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) := by
  sorry

example (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  sorry
