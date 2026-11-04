import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use
import Lean.Meta.Tactic.Refl

/-! **Lean Proofs**
  Last assignment, we worked with some tactics that behave similarly to our propositional
  logic formal deduction proof rules. Here, we will continue using the tactics we did before, but
  we will also see how to use them for formal first order logic proofs (as well as new tactics).

  In Lean, our propositional logic formulas were terms of type `Prop`.
  In first order logic, we require
    - a domain
    - individual symbols + free variables
    - relations
    - functions
  We can accomplish this using types, and maps `→` from the domain to `Prop` -/

/- Our domain can be an arbitrary type, where elements of the domain are terms of its type: -/
variable {α : Type*} -- `α` is our domain
variable {a b : α} -- `a` and `b` are terms of type `α`, or elements of our domain

/- Then for relations, we map from `a` into `Prop`. -/
variable {F G H : α → Prop} -- `F`, `G`, `H` are all maps from `α` to `Prop`.

/- As in the previous assignment, your goal is to replace the
  `sorry`s with proofs in a way where Lean will not give you errors.-/


/- **Section 1: For All**

  `intros a` - we used this before for `→` statements, but we can also use this when the goal is
    of the form `⊢ ∀ x, F x`, where `F : α → Prop`. When we use `intros` it adds `a : α` to our
    premise set, and our goal becomes `⊢ F a`.

    In this way, `intros` behaves like `(∀+)`.

  `specialize h a` - if we have a hypothesis `h : ∀ x, F x` where `F : α → Prop`, and term
    `a : α`, then `specialize h a` plugs `a` into the for all statement to obtain new premise
    `h : F a`.

     This is similar to `(∀-)`, but note that `specialize` works on premises, whereas
     `(∀-)` works on previous conclusions.

  *Note:* you actually don't really need `specialize` as a separate tactic - if you have
    `h : ∀ x, F x` where `F : α → Prop`, and you have term `a : α`, then `h a` will already be
    a term of type `F a`, i.e. `h a : F a`. This also works for implication, if `h : A → B` and
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

/- **For All Exercises** -/
example : ∀ x, F x → F x := by
  sorry

example (hFG : (∀ x, F x) ∧ (∀ x, G x)) : ∀ x, (F x ∧ G x) := by
  sorry

example (hFG : ∀ x, (F x ∧ G x)) : (∀ x, F x) ∧ (∀ x, G x) := by
  sorry

example (hFG : (∀ x, F x) ∨ (∀ x, G x)) : ∀ x, (F x ∨ G x) := by
  sorry

/- **Section 2: There Exists**

  `use` - When we have a goal of the form `⊢ ∃ x, F x` where `F : α → Prop`, and a term `a : α`,
    the tactic `use a` will replace the goal with `⊢ F a`.

    This tactic behaves like `(∃+)`.

  `obtain ⟨a, hFa⟩ := hF`- if we have premise `hF : ∃ x, F x` where `F : α → Prop`, this will
    break `hF` down to produce terms `a : α` and `hFa : F a` in our premise set.

    This tactic behaves like `(∃-)`.

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

/- **Exists Exercises** -/
example (hFG : ∃ x, F x ∨ G x) : (∃ x, F x) ∨ (∃ x, G x) := by
  sorry

example (hFG : ∃ x, F x ∧ G x) : (∃ x, F x) ∧ (∃ x, G x) := by
  sorry

example (hFG : (∃ x, F x) ∨ (∃ x, G x)) : ∃ x, F x ∨ G x := by
  sorry


/- **Section 3: Equals**

  `rw` - also known as "rewrite". If you have premise `h : t₁ = t₂` and goal `⊢ A(t₁)`, then
    `rw [h]` will replace the goal with `A(t₂)`. You can also rewrite backwards with `rw [← h]`.

    This behaves like `(≈-)`.

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

/- **Equals Exercises** -/
example (hab : a = b) (hFG : ∀ x, F x → G x) (hFa : F a) : G b := by
  sorry

example (hFa : F a) : ∃ x, x = a → F x := by
  sorry


/- **Section 4: DeMorgan's Laws for Quantifiers** -/
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

/- **Section 5: Additional Exercises** -/
/- **Another note on `rw`**
  We can actually also use `rw` for `iff` statements. We haven't used them much in our Lean
  homework assignments, but if we can prove an iff statement, we can use it together with
  `rw` similarly to our replaceability theorem in formal deduction.

  With our DML theorems, we can swap out one premise for another. Try using `rw` with our theorems
  `DML_1` and `DML_2` (or you can prove these directly). -/
example (hF : ¬ ∀ x, F x) (hFG : ∀ x, (¬ F x → G x)) : ∃ x, G x := by
  sorry

example (hF : ¬ ∃ x, F x) (hFG : ∀ x, (¬ F x → G x)) : ∀ x, G x := by
  sorry

-- Note: you don't need `by_contra` or `DML` for this one
example (hFH : (∀ x, F x) → (∃ x, H x)) (hFG : ∀ x, (F x ∧ G x)) : ∃ x, H x := by
  sorry

variable {R : α → α → Prop} -- this is one way we can define relations with multiple arguments.
-- By Curry-Howard correspondence, the type is equivalent to `α × α → Prop`.

example (hR : ∃ y, ∀ x, R x y) : ∀ x, ∃ y, R x y := by
  sorry
