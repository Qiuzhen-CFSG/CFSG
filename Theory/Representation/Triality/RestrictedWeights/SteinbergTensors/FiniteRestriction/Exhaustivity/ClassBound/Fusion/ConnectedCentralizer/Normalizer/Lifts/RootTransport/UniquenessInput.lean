module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Geometry

/-!
# Uniqueness input for actual D4 root subgroups

The realization indexes exactly the actual root characters and chooses a
subgroup for each character. It does not itself assert uniqueness of that
subgroup. This predicate states precisely the remaining geometric input for
normalizer transport, independently of the normalizer map and simple words.
Its construction from `Geometry` remains a separate proof obligation.

Source: GLS3, `refs/KGroup/GLS3/Chapter1.tex`, Theorem 1.9.5(b).
-/

@[expose] public section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup
namespace ConnectedCentralizer.Normalizer
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Uniqueness at the realized root weights is the remaining geometric
input needed for identifying the normalizer conjugates. -/
def RootSubgroupUniqueness (S : Geometry K) : Prop :=
  ∀ (a : S.roots.Root) (X : ClosedSubgroup K),
    IsTorusRootSubgroup S.torus X →
    RootWeightEquation S.torus X (S.roots.rootWeight a) →
    X = S.roots.rootSubgroup a

end ConnectedCentralizer.Normalizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
