module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

/-!
# Elementary actors preserving an embedded six-letter alternating group

These interfaces specify a concrete subgroup of automorphisms, an embedded
A₆, and an actual Sylow subgroup of A₆ fixed pointwise by every actor.
The actor group has order eight; its pointwise fixer on A₆ has order two
and contains an outer automorphism. The remaining binary-linear calculation
asks for a nonidentity actor fixing a Sylow subgroup of the entire group.

This is the intrinsic model input used in Aschbacher–Smith, combined manuscript
(1 March 2004), E.6.23, printed p.254 (PDF p.265). The definitions assert no
existence or classification theorem.
-/

@[expose] public section

open Subgroup MulAction
namespace BinaryLinear.SixSylowActors
variable {Y : Type*} [Group Y]

/-- The genuine action and Sylow arrangement, before choosing a two-central actor. -/
structure Configuration (E : Subgroup (MulAut Y)) (D : Subgroup Y) : Prop where
  elementary : IsElementaryAbelian 2 E
  card : Nat.card E = 8
  six : Nonempty (D ≃* alternatingGroup (Fin 6))
  stable : ∀ a ∈ E, D.map a.toMonoidHom = D
  fixer_card : Nat.card ↥(E ⊓ fixingSubgroup (MulAut Y) (D : Set Y)) = 2
  fixer_outer : ¬ E ⊓ fixingSubgroup (MulAut Y) (D : Set Y) ≤
    (MulAut.conj : Y →* MulAut Y).range
  sylow : ∃ Q : Sylow 2 D, ∀ a ∈ E, ∀ x ∈ (Q : Subgroup D), a (x : Y) = x

/-- The specific model fact needed to lift a line of actors to a subspace. -/
def HasTwoCentralActor (Y : Type*) [Group Y] : Prop :=
  ∀ (E : Subgroup (MulAut Y)) (D : Subgroup Y), Configuration E D →
    ∃ a ∈ E, a ≠ 1 ∧ ∃ P : Sylow 2 Y, ∀ x ∈ (P : Subgroup Y), a x = x

end BinaryLinear.SixSylowActors
