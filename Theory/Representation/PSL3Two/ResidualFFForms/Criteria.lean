module

public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.RepresentationTheory.Irreducible

/-!
# A single actor's obstruction on simple constituents

`SimpleBudget A d` records the two constituent facts used to rule out invariant
forms on nonsplit modules with fixed codimension at most `d`: every affordable
nontrivial simple module is inequivalent to its dual, and its cost together
with its dual's cost exceeds `d`. All codimensions use the same subgroup `A`.

This numerical interface separates the concrete binary SL₃(2) catalogue from
the induction on arbitrary finite-dimensional modules. It does not assert
that the criterion holds for a given group or actor.

Source: the constituent argument of Meierfrankenfeld–Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), (1.4) and (3.8), printed
pp.842 and 878.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace BinaryLinearThree.ResidualFFForms

universe u v

/-- The simple constituents affordable for one actor are not self-dual, and a
constituent together with its dual exceeds that same actor's budget. -/
def SimpleBudget {G : Type v} [Group G] (A : Subgroup G) (d : ℕ) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) G W),
    IsIrreducible σ → σ ≠ 1 → fixedCodim σ A ≤ d →
      (¬ Nonempty (σ.Equiv σ.dual)) ∧
        d < fixedCodim σ A + fixedCodim σ.dual A


end BinaryLinearThree.ResidualFFForms
