module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointGeometry

/-!
# The two remaining source obligations in the exterior Hall argument

These propositions separate the specialized A.3.15 action argument from
Chapter 4 odd-normalizer control. Both use the full chosen module V. The
point V₁ is used only to obtain normalization of V from 12.2.6.

Neither proposition is proved here. Hall.Primitive constructs the actual
prime omega subgroup of the E.2.2 Hall subgroup, proves its Sylow permutation
property, and combines the two propositions with the proved 4.4.13 escape.
Hall.lean retains both premises until their source proofs are supplied.

Source: Aschbacher--Smith, 12.2.11(a), printed pp.798--799;
A.3.15, pp.50--51; 4.4.3, pp.619--622.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource

universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- The PSL₅(2) specialization of the action exclusion in 12.2.11(a).
The quotient marking is part of s; the action is literal conjugation on V.
This is a construction target, not an earlier theorem. -/
def ExteriorOddActionCentralizes (s : SylowExteriorMarking D) : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ A : Subgroup G,
    A ≠ ⊥ → IsElementaryAbelian p A → A ≤ s.marking.M →
    A ≤ normalizer (V : Set G) →
    (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) →
    A ≤ centralizer (V : Set G)

/-- The PSL₅(2) specialization of 4.4.3 needed after the action exclusion.
Its source proof must establish the section-centralizer premise and exclude
the exceptional model rows; those conclusions are not assumed in this target. -/
def ExteriorOddNormalizerControl (s : SylowExteriorMarking D) : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ A : Subgroup G,
    A ≠ ⊥ → IsElementaryAbelian p A → A ≤ s.marking.M →
    A ≤ centralizer (V : Set G) → normalizer (A : Set G) ≤ s.marking.M

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
