module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Equivariant binary quadratic maps with a dual pairing

This interface records a binary quadratic map between two elementary groups,
together with an invariant nondegenerate pairing. In the class-three group
application the two groups are the abelianization and the derived group modulo
the center; the map is squaring and the pairing is the central commutator.

The seven-term identity expresses quadraticity without choosing coordinates.
The additional zero records an involution outside the derived subgroup.
Existence of this data, and consequences of particular acting groups, are
separate mathematical assertions.

Source: the square and commutator constructions in Parrott (1972), pp.673–674.
-/

namespace Theory.GroupAction

/-- A square map and its central pairing, equivariant under a supplied action.
Cardinalities and elementary exponents are imposed by its consumers. -/
public structure BinaryQuadraticPairing (A V W : Type*)
    [Group A] [Group V] [Group W] where
  pairing : V →* (W →* Multiplicative (ZMod 2))
  pairing_injective : Function.Injective pairing
  square : V → W
  square_one : square 1 = 1
  square_quadratic : ∀ a b c : V,
    square (a * b * c) * square (a * b) * square (a * c) *
      square (b * c) * square a * square b * square c = 1
  square_self : ∀ v : V, pairing v (square v) = 1
  square_has_nontrivial_zero : ∃ v : V, v ≠ 1 ∧ square v = 1
  leftAction : A →* MulAut V
  rightAction : A →* MulAut W
  leftAction_injective : Function.Injective leftAction
  rightAction_injective : Function.Injective rightAction
  pairing_equivariant : ∀ a v w,
    pairing (leftAction a v) (rightAction a w) = pairing v w
  square_equivariant : ∀ a v, square (leftAction a v) = rightAction a (square v)

end Theory.GroupAction
