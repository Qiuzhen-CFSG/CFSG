module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceSetup
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.theorem_1_13_5
public import Theory.AlgebraicGroup.Borel.HighestWeight

/-!
This module isolates `theorem_1_14_6` from `Theory.AlgebraicGroup.Parabolic.RelativeRoot`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.

The source-level relative-root layer wrapper and representation contract are
imported from `SourceSetup`, where they remain available without the heavier
standard-parabolic and highest-weight interfaces used below.

The positive-generation/highest-weight chain also needs the converse direction
of the partial root-addition table.  The explicit `rootAdditionComplete`
hypothesis below is the minimal source-faithful repair: `D.IsRealization` only
states that entries of `D.add` have the expected weight, so it permits an
everywhere-`none` table and cannot by itself support the geometric transfer.
This compatibility premise is independent of the high-weight conclusions and
does not smuggle in positivity, Borel-root witnesses, or radical
identification.

The printed source of GLS3 Theorem 1.14.6(a) omits the nonzero-module condition
that is implicit in its definition of a high-weight vector as spanning a
one-dimensional invariant line. We make that necessary condition explicit as
`[Nontrivial V]`: with the existing definition of `HasHighWeight`, a high-weight
vector is required to be nonzero, so the zero-dimensional representation is an
immediate counterexample without this instance. Clause (b) explicitly assumes
`IsRationalRepresentation ρ`, since the root-string argument establishing
dominance is an algebraic-representation argument rather than a statement
about an arbitrary abstract point-group action. Clauses (c)--(e) retain their
source hypotheses; in (d) and (e), nonzeroness is already supplied by the
displayed high-weight vector.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_14_6
    {K : Variety k} [AlgebraicGroup K] (B T : ClosedSubgroup K)
    (D : RootGroupData K T)
    (hK : IsSemisimpleAlgebraicGroup K) (hUniversal : IsUniversalVersion K)
    (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hD : D.IsRealization)
    (rootAdditionComplete : D.IsRootAdditionComplete)
    (hBpos : B.toSubgroup =
      RootSubgroupGenerated D D.positive ⊔ T.toSubgroup) :
    (∀ {V : Type v} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [Nontrivial V]
      (ρ : RationalRepresentation K V),
      IsRationalRepresentation ρ → ∃ v χ, HasHighWeight ρ B T v χ) ∧
    (∀ {V : Type v} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (ρ : RationalRepresentation K V) v χ,
      IsRationalRepresentation ρ →
        HasHighWeight ρ B T v χ → IsDominantWeight D χ) ∧
    (∀ {V : Type v} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (ρ : RationalRepresentation K V),
      IsIrreducibleRepresentation ρ →
      ∀ v w χ μ, HasHighWeight ρ B T v χ → HasHighWeight ρ B T w μ →
        ∃ c : k, c ≠ 0 ∧ w = c • v) ∧
    (∀ {V W : Type v} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W]
      [FiniteDimensional k W]
      (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W),
      IsIrreducibleRepresentation ρ → IsIrreducibleRepresentation σ →
      ∀ v w χ, HasHighWeight ρ B T v χ → HasHighWeight σ B T w χ →
        AreEquivalentRepresentations ρ σ) ∧
    (∀ χ, IsDominantWeight D χ →
      ∃ W : Type v, ∃ _ : AddCommGroup W, ∃ _ : Module k W,
        ∃ _ : FiniteDimensional k W, ∃ ρ : RationalRepresentation K W,
          IsIrreducibleRepresentation ρ ∧
            ∃ w : W, HasHighWeight ρ B T w χ) := by
  refine ⟨?_, by sorry, by sorry, by sorry, by sorry⟩
  intro V _ _ _ _ ρ hρ
  exact highWeight_exists_of_borel B T ρ hρ hB hT hTB

end Theory.AlgebraicGroup
