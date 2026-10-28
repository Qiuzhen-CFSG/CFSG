module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_5
public import Theory.AlgebraicGroup.Borel.RootStructure.UnipotentProductDefs

/-!
The explicit center generators of GLS3 Theorem 1.12.6 and the root-product
interfaces used by Theorem 1.12.7.

The re-exported root-product definitions record that `RootGroupData.add` is
actual root addition in its chosen root-system realization. Their membership
lemmas convert a source-style root-vector equality into a declared `D.add`
equation before applying the existing positive-system, closed-subset, or root-
ideal axiom. This excludes the everywhere-`none` addition operation while
preserving the established root-data predicates and their consumers.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_12_6
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSimpleAlgebraicGroup K)
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (C : ChevalleyData K D)
    (hT : IsMaximalTorus T) (hD : D.IsRealization)
    (hTGenerated :
      T.toSubgroup = Subgroup.closure {g | ∃ α t, g = C.h α t})
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hActual : IsRootSystemRealization D P e base)
    (hC : IsChevalleySystem D C P e base)
    (classification : RootClassification)
    (hValid : IsValidGeneratorTableClassification classification)
    (numbered : NumberedDynkinBase P base classification) :
    Subgroup.center (Variety.Point K) =
      Subgroup.closure (centerGeneratorTable C e classification numbered) := by sorry

public def EnumeratesType {ι : Type*} (order : List ι) : Prop :=
  order.Nodup ∧ ∀ i, i ∈ order

@[expose]
public def FundamentalRoot
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root) :=
  {α : D.Root // α ∈ FundamentalRootsFor D positiveRoots}

public structure SimpleRootTorusFamily
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (positiveRoots : Set D.Root) where
  carrier : FundamentalRoot D positiveRoots → ClosedSubgroup K
  mem_iff : ∀ α t,
    t ∈ carrier α ↔
      t ∈ T ∧
        ∀ β : FundamentalRoot D positiveRoots, β ≠ α →
          t ∈ Subgroup.centralizer
            ((D.rootSubgroup β.1).toSubgroup : Set (Variety.Point K))

public def IsOneDimensionalTorusModuloAmbientCenter
    {K : Variety k} [AlgebraicGroup K] (A : ClosedSubgroup K) : Prop :=
  ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
    (q : @AlgebraicGroup.Morphism k _ A.carrierVariety Q
      A.carrierAlgebraicGroup _),
      Function.Surjective q.onPoints ∧
      q.kernel =
        (Subgroup.center (Variety.Point K)).comap A.inclusion.onPoints ∧
      IsTorus Q ∧ Variety.dimension Q = 1

public def orderedSubgroupFactorProduct
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {positiveRoots : Set D.Root}
    (_family : SimpleRootTorusFamily D positiveRoots)
    (order : List (FundamentalRoot D positiveRoots))
    (factors : Fin order.length → Variety.Point K) : Variety.Point K :=
  (List.ofFn factors).prod

public structure BorelRootStructure
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root) (B U : ClosedSubgroup K)
    (C : ChevalleyData K D)
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base) where
  root_addition_realization : IsRootAdditionRealization D P e
  ordered_factorization : ∀ order, EnumeratesRootSet positiveRoots order →
    ∀ u, u ∈ U ↔
      ∃! parameters : Fin order.length → k,
        orderedChevalleyProduct C order parameters = u
  commutator_formula : ∀ α β, α ∈ positiveRoots → β ∈ positiveRoots →
    ∀ order,
      EnumeratesRootSet (PositiveRootCombinations (D := D) P e α β) order →
        ∀ g,
          g ∈ ⁅(D.rootSubgroup α).toSubgroup,
            (D.rootSubgroup β).toSubgroup⁆ →
          g ∈ OrderedRootSubgroupProductFin D order
  closed_subset : ∀ roots, roots ⊆ positiveRoots → IsClosedRootSubset D roots →
    Nonempty (ClosedRootProduct (U := U) D roots)
  ideal_subset : ∀ roots, IsRootIdealIn D positiveRoots roots →
    Nonempty (NormalRootProduct (U := U) D roots)
  fundamental_generation :
    U.toSubgroup = RootSubgroupGenerated D (FundamentalRootsFor D positiveRoots)
  simple_tori : SimpleRootTorusFamily D positiveRoots
  simple_tori_centralizer : ∀ α,
    (simple_tori.carrier α).toSubgroup ⊓
        Subgroup.centralizer
          ((D.rootSubgroup α.1).toSubgroup : Set (Variety.Point K)) =
      Subgroup.center (Variety.Point K)
  simple_tori_quotient : ∀ α,
    IsOneDimensionalTorusModuloAmbientCenter (simple_tori.carrier α)
  torus_product : ∀ order, EnumeratesType order → ∀ t, t ∈ T →
    ∃ factors : Fin order.length → Variety.Point K,
      (∀ i, factors i ∈ simple_tori.carrier (order.get i)) ∧
        orderedSubgroupFactorProduct simple_tori order factors = t
  adjoint_torus_direct : IsAdjointVersion K →
    ∀ order, EnumeratesType order → ∀ t, t ∈ T →
      ∃! factors : Fin order.length → Variety.Point K,
        (∀ i, factors i ∈ simple_tori.carrier (order.get i)) ∧
          orderedSubgroupFactorProduct simple_tori order factors = t

end Theory.AlgebraicGroup
