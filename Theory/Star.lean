module

public import Mathlib.Algebra.Notation.Defs

@[expose] public section

universe u

/-- `star` distributes over an `if` expression. -/
public lemma star_ite {R : Type u} [Star R] {p : Prop} [Decidable p] (a b : R)
    : star (if p then a else b) = (if p then star a else star b) := by
  by_cases h : p <;> simp [h]
