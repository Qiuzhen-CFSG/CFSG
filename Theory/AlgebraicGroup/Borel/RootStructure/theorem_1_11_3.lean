module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_11_2

/-!
This module isolates `theorem_1_11_3` from `Theory.AlgebraicGroup.Borel.RootStructure`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_11_3
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsReductiveAlgebraicGroup K)
    (T B : ClosedSubgroup K)
    (D : RootGroupData K T) (positiveRoots : Set D.Root)
    (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (hBroot : B.toSubgroup =
      RootSubgroupGenerated D positiveRoots ⊔ T.toSubgroup)
    {ι X Y : Type u} [Finite ι]
    [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots) :
    ∃ TS : { TS : TitsSystem (X := Variety.Point K) //
        (TS.B, TS.N) =
          (B.toSubgroup, Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))) },
      ∃ weylEquiv :
          (TS.1.N ⧸ (TS.1.B ⊓ TS.1.N).subgroupOf TS.1.N) ≃* P.weylGroup,
        ∀ s, s ∈ TS.1.S ↔
          ∃ i : base.support, weylEquiv s = base.simpleReflection i := by sorry

public structure BorelIntersectionDecomposition
    {K : Variety k} [AlgebraicGroup K]
    (B₀ B₁ U₀ U₁ : ClosedSubgroup K) where
  torus : ClosedSubgroup K
  maximalTorus : IsMaximalTorus torus
  factorization :
    (B₀.inter B₁).toSubgroup =
      torus.toSubgroup ⊔ (U₀.inter U₁).toSubgroup

end Theory.AlgebraicGroup
