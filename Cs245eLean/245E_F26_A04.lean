import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use
import Lean.Meta.Tactic.Refl

/-! **Lean Proofs**
  Last assignment, we worked with some tactics that behave similarly to our propositional
  logic formal deduction proof rules. Here, we will see how to use tactics for formal
  first order logic proofs. As in the previous assignment, your goal is to replace the
  `sorry`s with proofs in a way where Lean will not give you errors.

  Our limited tactic list for this assignment will be the following.-/

variable {α : Type*} -- `α` can be viewed as our domain
variable {a b : α} -- `a` and `b` are terms of type `α`, or elements of our domain
variable {F G H : α → Prop} -- we can think of relations as maps from the domain to `Prop`

/- **For All**

  `intros a` - we can also use this when the goal is of the form `⊢ ∀ x, F x`.
    If `F` is a relation on terms of type `α`, i.e. `F : α → Prop`, then when
    we use `intros` it adds `a : a` to our premise set and our goal becomes `⊢ F a`.
    In this way, `intros` also behaves like `(∀+)`.
  `specialize h a` - if we have a hypothesis `h` of the form `h : ∀ x, F x`, and
    term `a : α` whose type matches the domain of `F : α → Prop`, then `specialize h a`
     plugs `a` into the for all statement to transform `h` into the premise `h : F a`.
     This is similar to `(∀-)`, but note that we don't require explicitly showing
     the for all statement as a consequence of our premises, we can just use it
     directly on the premise in question.
  *Note:* you actually don't really need `specialize` as a separate tactic - if you have
    `h : ∀ x, F x` where `F : α → Prop`, and you have term `a : α`, then `h a` will already be
    a term of type `F a`, i.e. `h : F a`. This also works for implication, if `h : A → B` and
    you have a term `a : A`, then `h a : B`.
 -/

/- **Examples** -/
example (hFG : ∀ x, F x → G x) (hF : ∀ x, F x) : ∀ x, G x := by
  intros a
  specialize hF a
  apply hFG
  exact hF

-- alternate proof that doesn't use `specialize`
example (hFG : ∀ x, F x → G x) (hF : ∀ x, F x) : ∀ x, G x := by
  intros a
  apply hFG
  exact hF a

/- **Exercises** -/
example : ∀ x, F x → F x := by
  sorry

example (hFG : (∀ x, F x) ∧ (∀ x, G x)) : ∀ x, (F x ∧ G x) := by
  sorry

example (hFG : ∀ x, (F x ∧ G x)) : (∀ x, F x) ∧ (∀ x, G x) := by
  sorry

example (hFG : (∀ x, F x) ∨ (∀ x, G x)) : ∀ x, (F x ∨ G x) := by
  sorry

/- **There Exists**

  `use` - this behaves like `(∃+)`. When we have a goal of the form `⊢ ∃ x, F x` where
    `F : α → Prop`, and a term `a : α`, the tactic `use a` will replace the goal with
    `⊢ F a`.
  `obtain ⟨a, hFa⟩ := hF`- if we have premise `hF : ∃ x, F x` where `F : α → Prop`, this will
    break it down to produce terms `a : α` and `hFa : F a` in our premise set.
    *Note:* We are again using the angle bracket syntax here - this is because it can also be
      used as a constructor for ∃ statements. As an alternative to `use`, we can actually use
      the `refine ⟨a, hFa⟩` tactic if we want to.
    - constructors can actually be nested - if we wanted to break down something like
      `hFG : ∃ x, F x ∨ G x` using `obtain`, we could say `obtain ⟨a, hFa | hGa⟩ := hFG`.
    - Lean is powerful enough to infer a lot of stuff for us too. For example, if our goal is
      `⊢ ∃ x, F x` and we want to close it using term `a : α` and premise `hFa : F a`, we can
      actually just use `refine ⟨_, hFa⟩` and Lean will infer the term `a`.
      The underscore `_` can be used to indicate to Lean a "proof hole," i.e. something we want
      it to infer on its own.
  -/

/- **Examples** -/
example (hFG : ∀ x, F x → G x) (hF : ∃ x, F x) : ∃ x, G x := by
  obtain ⟨a, ha⟩ := hF
  use a
  exact hFG a ha

-- alternate proof with `refine`
example (hFG : ∀ x, F x → G x) (hF : ∃ x, F x) : ∃ x, G x := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨a, hFG a ha⟩

-- alternate proof with `refine` with a proof hole
example (hFG : ∀ x, F x → G x) (hF : ∃ x, F x) : ∃ x, G x := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨_, hFG a ha⟩

/- **Exercises** -/
example (hFG : ∃ x, F x ∨ G x) : (∃ x, F x) ∨ (∃ x, G x) := by
  sorry

example (hFG : ∃ x, F x ∧ G x) : (∃ x, F x) ∧ (∃ x, G x) := by
  sorry

example (hFG : (∃ x, F x) ∨ (∃ x, G x)) : ∃ x, F x ∨ G x := by
  sorry


/- **Equals**

  `rw` - also known as "rewrite". This behaves like `(≈-)`. If you have premise `h : t₁ = t₂` and
    `⊢ A(t₁)`, then `rw [h]` will replace the goal with `A(t₂)`. You can also rewrite backwards
    with `rw [← h]`.
    *Note:* `rw` also works on premises - if we have premise `hA : A(t₁)`
    then `rw [h] at hA` will change it to `hA : A(t₂)`.
  `rfl`- if the goal is of the form `⊢ u = u` then `rfl` will simply close the goal, like `(≈+)`.
    *Note:* A lot of the time, we actually won't necessarily see `⊢ u = u` in the goal - if we
    got to that point via `rw`, the `rw` tactic actually itself applies `rfl`, so it will often
    close the goal for us.
-/

/- **Examples** -/
example : a = a := by
  rfl

/- **Exercises** -/
example (hab : a = b) (hFG : ∀ x, F x → G x) (hFa : F a) : G b := by
  sorry

example (hFa : F a) : ∃ x, x = a → F x := by
  sorry


/- **Another note on `rw`**
  We can actually also use `rw` for `iff` statements. We haven't used them much in our Lean
  homework assignments, but if we can prove an iff statement, we can use it together with
  `rw` similarly to our replaceability theorem in formal deduction.
-/


/- **DeMorgan's Laws for Quantifiers** -/
-- *Note:* you will need to use `by_contra` for some of these problems.
theorem DML_helper_1 (hF : ¬ ∃ x, F x) : ∀ x, ¬ F x := by
  sorry

theorem DML_helper_2 (hF : ∀ x, ¬ F x) : ¬ ∃ x, F x := by
  sorry

theorem DML_helper_3 (hF : ¬ ∀ x, F x) : ∃ x, ¬ F x := by
  sorry

theorem DML_helper_4 (hF : ∃ x, ¬ F x) : ¬ ∀ x, F x := by
  sorry

-- Putting these together, we have the following:
theorem DML_1 : (¬ ∃ x, F x) ↔ (∀ x, ¬ F x) :=
  ⟨fun h => DML_helper_1 h, fun h => DML_helper_2 h⟩

theorem DML_2 : (¬ ∀ x, F x) ↔ (∃ x, ¬ F x) :=
 ⟨fun h => DML_helper_3 h, fun h => DML_helper_4 h⟩

-- note the angle bracket constructors - in Lean, we can construct an `↔` statement by providing
-- both directions. One constructor we haven't touched on is `fun h => ?_`, which behaves
-- like an inline version of `intros` for both `→` and `∀` statements.

/- With these theorems, we can swap out one premise for another. Try using `rw` with our theorems
  `DML_1` and `DML_2` (or you can prove these directly). -/
example (hF : ¬ ∀ x, F x) (hFG : ∀ x, (¬ F x → G x)) : ∃ x, G x := by
  sorry

example (hF : ¬ ∃ x, F x) (hFG : ∀ x, (¬ F x → G x)) : ∀ x, G x := by
  sorry

/- **Additional Exercises** -/
-- Note: you don't need `by_contra` or `DML` for this one
example (hFH : (∀ x, F x) → (∃ x, H x)) (hFG : ∀ x, (F x ∧ G x)) : ∃ x, H x := by
  sorry

variable {R : α → α → Prop} -- this is one way we can define relations with multiple arguments.
-- By Curry-Howard correspondence, the type is equivalent to `α × α → Prop`.

example (hR : ∃ y, ∀ x, R x y) : ∀ x, ∃ y, R x y := by
  sorry
