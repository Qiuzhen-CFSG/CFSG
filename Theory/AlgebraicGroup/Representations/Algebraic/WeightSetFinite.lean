module

public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A finite-dimensional representation has only finitely many
nonzero torus weight spaces. -/
public theorem representationWeights_finite
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K) :
    (representationWeights ρ T).Finite :=
  Submodule.finite_ne_bot_of_iSupIndep (weightSpace_iSupIndep ρ T)

end Theory.AlgebraicGroup
