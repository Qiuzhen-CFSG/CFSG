module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Geometry

/-!
# Statements of the finite restricted-weight obligations

These predicates specify the three separate conclusions of GLS3 Theorem 2.8.2
on actual representations. They are not assumptions in `Geometry` and are not
asserted as theorems here. Keeping the statements separate permits the counting
or extension proof of exhaustivity to use proved irreducibility and separation
without imposing an order on their proofs.
-/

@[expose] public section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual positive-root subgroup intersected with the elementary group. -/
def positiveUnipotent (S : Geometry K) (n : ℕ) :
    Subgroup (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :=
  (RootSubgroupGenerated S.roots S.roots.positive).comap (S.inclusion n)

/-- Restricted rational irreducibles remain irreducible on the elementary group. -/
def RestrictedIrreducibility (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A : RationalFactor K) (a : Weight),
    InRestrictedRange n a → HasHighestWeight S A a →
      Representation.IsIrreducible (A.restrict (S.inclusion n)).ρ

/-- A genuine intertwiner of finite restrictions cannot identify distinct
restricted highest weights. The reverse implication is already proved. -/
def RestrictedSeparation (S : Geometry K) (n : ℕ) : Prop :=
  ∀ (A C : RationalFactor K) (a b : Weight),
    InRestrictedRange n a → InRestrictedRange n b →
      HasHighestWeight S A a → HasHighestWeight S C b →
        Nonempty (Representation.Equiv (A.restrict (S.inclusion n)).ρ
          (C.restrict (S.inclusion n)).ρ) → a = b

/-- Every irreducible elementary-group module has an actual restricted
rational lift, with a linear intertwining equivalence. -/
def RestrictedExhaustivity (S : Geometry K) (n : ℕ) : Prop :=
  ∀ V : FDRep k (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n),
    Representation.IsIrreducible V.ρ →
      ∃ (A : RationalFactor K) (a : Weight),
        InRestrictedRange n a ∧ HasHighestWeight S A a ∧
          Nonempty (Representation.Equiv V.ρ (A.restrict (S.inclusion n)).ρ)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
