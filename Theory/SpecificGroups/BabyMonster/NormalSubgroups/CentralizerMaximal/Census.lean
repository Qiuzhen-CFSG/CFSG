module

public import Theory.SpecificGroups.BabyMonster.NormalSubgroups.Generation
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fin.VecNotation

/-!
# The double-coset census needed for the Baby Monster centralizer

Breuer–Magaard–Wilson (2019), §5.2, https://arxiv.org/abs/1902.07758,
list five suborbits of a 2A centralizer, including its fixed point. Multiplying
these subdegrees by the centralizer order gives the double-coset sizes.

This module specifies that census for the fixed eleven-generator presentation.
It makes no existence assertion: constructing the labeling and proving its
fiber sizes for this presentation is a separate mathematical obligation.
The maximality criterion consumes such a census explicitly.
-/

public section
namespace BabyMonster

/-- The fixed point and the four nontrivial subdegrees, in the source's order. -/
@[expose] def generatorCentralizerSubdegree : Fin 5 → ℕ :=
  ![1, 3968055, 23113728, 2370830336, 11174042880]

/-- A labeling of the actual presentation's double cosets, with their sizes.
Existence of this data must be proved from the presentation or a verified model. -/
structure GeneratorCentralizerDoubleCosetCensus where
  label : Carrier → Fin 5
  label_one : label 1 = 0
  same_label_iff : ∀ x y : Carrier, label x = label y ↔
    ∃ a ∈ generatorCentralizer, ∃ b ∈ generatorCentralizer, y = a * x * b
  card_fiber : ∀ i, Nat.card {x : Carrier // label x = i} =
    generatorCentralizerSubdegree i * Nat.card generatorCentralizer

end BabyMonster
