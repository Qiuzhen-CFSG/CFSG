module

public import Theory.AlgebraicGroup.RootData.RelativeRoots
public import Theory.AlgebraicGroup.Borel.Defs

universe u

/-!
Standard Borel and parabolic configurations attached to root data.

`IsStandardBorelSetup` packages the maximal torus, realized root data,
positive system, and Borel containment used by the standard constructions.
Its final field records the converse direction for the partial root-addition
operation: every actual sum of two root weights is represented by `D.add`.
This completeness clause is independent of the forward addition equation in
`RootGroupData.IsRealization`; it rules out degenerate addition tables while
leaving the existing geometric and root-system fields unchanged.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def IsStandardBorelSetup
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    (D : RootGroupData K T) (positiveRoots : Set D.Root) : Prop :=
  IsMaximalTorus T ∧ D.IsRealization ∧ IsPositiveSystem D positiveRoots ∧
    IsBorelSubgroup B ∧ T ≤ B ∧ D.IsRootAdditionComplete

@[expose]
public def IsStandardParabolicSetup
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    (D : RootGroupData K T) (positiveRoots J sigmaJ : Set D.Root) : Prop :=
  IsStandardBorelSetup T B D positiveRoots ∧
    J ⊆ D.simple ∧
    sigmaJ = RootSubsystemSpan D J

end

end Theory.AlgebraicGroup
