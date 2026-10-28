module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.RepresentationTheory.Intertwining
public import Theory.PGroupCore
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryNaturalDual.Action

/-!
# Literal chief-action targets in the noncore branch of 15.2.27

These finite linear-action models specify group isomorphisms and actual intertwining
maps. In particular the natural-plus-dual row includes the graph action,
and the paired row includes the factor-exchanging element of the wreath
product. The moving-parabolic structure is an output contract. No recognition
or existence theorem is asserted here. The source application uses the
quotient of the image of H by its own two-core; that image need not itself
be the order-72 wreath group.

Source: Aschbacher--Smith, 15.2.27(2), printed p.1119.
-/

@[expose] public section
open Subgroup Representation
namespace Representation.SmallDisplacementParabolics

abbrev PairIndex := Multiplicative (ZMod 2)
abbrev ThreeSpace := Fin 3 → ZMod 2
abbrev PairedActor := RegularWreathProduct (BinaryLinear.OuterCyclic.LinearGroup 3) PairIndex

/-- The exact surviving modules, with their full actions. -/
def ActionModel {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) : Prop :=
  (∃ e : D ≃* Equiv.Perm (Fin 8),
    Nonempty (ρ.Equiv ((BinaryPermutation.naturalRepresentation (Fin 8)).comp e.toMonoidHom))) ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ∃ d : BinaryNaturalDual.CoordinateAction n,
    ∃ e : D ≃* MulAut (BinaryLinear.OuterCyclic.LinearGroup n),
      Nonempty (ρ.Equiv (d.representation.comp e.toMonoidHom))) ∨
  (∃ e : D ≃* PairedActor, ∃ E : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace),
    ∀ g w i, E (ρ g w) i = (e g).left i (E w ((e g).right⁻¹ * i)))

/-- Target of the concrete model calculation. Every proper subgroup over the
marked Sylow group normalizes it, and the two-residual moves the same vector. -/
structure MovingParabolic {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (S : Sylow 2 D) (w : W) where
  subgroup : Subgroup D
  sylow_le : (S : Subgroup D) ≤ subgroup
  proper : ∀ Y : Subgroup D, (S : Subgroup D) ≤ Y → Y < subgroup →
    Y ≤ normalizer (S : Set D)
  moves : ∃ g ∈ (pResidual 2 subgroup).map subgroup.subtype, ρ g w ≠ w

end Representation.SmallDisplacementParabolics
