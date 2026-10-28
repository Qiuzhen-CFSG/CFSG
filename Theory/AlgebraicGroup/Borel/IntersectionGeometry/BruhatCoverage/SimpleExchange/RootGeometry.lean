module

public import Theory.AlgebraicGroup.BNPair.SL2SimpleExchange
public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.RootSubgroups.TorusGeneratedNormalizer

/-!
Geometric inputs for simple-reflection exchange in a reductive group.

`SimpleExchangeRootGeometry` specifies actual root subgroups at the given torus
and homomorphisms from the matrix group `SL₂` onto the corresponding rank-one
groups. Their upper and lower images are identified with the ambient root
subgroups. Normalizer generation, the action of a simple reflection on the
other positive roots, and the root-sign alternative are recorded separately
from the local exchange conclusion.

`SimpleRootRemainderNormalization` is the independent commutator input: deleting
one simple root from the positive roots leaves a subgroup normalized by that
root subgroup. Together these inputs allow the consumer to collect that simple
root last and apply the checked matrix calculation. This file does not assert
existence of the geometric inputs.

Sources: GLS3, §§1.9–1.11, especially 1.11.3; Borel, §14.5 and §14.15 T2/T3.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

open scoped MatrixGroups

variable {k : Type u} [Field k]
    {G : Variety k} [AlgebraicGroup G] (B T : ClosedSubgroup G)

/-- The actual root and rank-one data used by the simple-exchange proof.
Existence from reductivity is a separate geometric theorem. -/
public structure SimpleExchangeRootGeometry where
  data : RootGroupData G T
  realized : data.IsRealization
  addition_complete : data.IsRootAdditionComplete
  positive : Set data.Root
  isPositive : IsPositiveSystem data positive
  borel : IsBorelOfPositiveSystem data positive B
  rankOne : {α // α ∈ FundamentalRootsFor data positive} →
    Matrix.SpecialLinearGroup (Fin 2) k →* Variety.Point G
  upper_range : ∀ i, Set.range (fun t => rankOne i (BruhatGeneration.SL2.upper t)) =
    (data.rootSubgroup i.val : Set (Variety.Point G))
  lower_range : ∀ i, Set.range (fun t => rankOne i (BruhatGeneration.SL2.lower t)) =
    (data.rootSubgroup (data.neg i.val) : Set (Variety.Point G))
  diagonal_mem : ∀ i t (ht : t ≠ 0),
    rankOne i (Matrix.SpecialLinearGroup.diag2 t ht) ∈ T.toSubgroup
  reflection_mem : ∀ i,
    rankOne i BruhatGeneration.SL2.reflection ∈ T.normalizer.toSubgroup
  normalizer_generated :
    Subgroup.closure ((T.toSubgroup : Set (Variety.Point G)) ∪
      Set.range (fun i => rankOne i BruhatGeneration.SL2.reflection)) =
        T.normalizer.toSubgroup
  reflection_other_positive : ∀ i β, β ∈ positive → β ≠ i.val →
    ∀ x ∈ (data.rootSubgroup β).toSubgroup,
      rankOne i BruhatGeneration.SL2.reflection * x *
        (rankOne i BruhatGeneration.SL2.reflection)⁻¹ ∈ B.toSubgroup
  transport_sign : ∀ i n, n ∈ T.normalizer.toSubgroup →
    (∀ t, n⁻¹ * rankOne i (BruhatGeneration.SL2.upper t) * n ∈ B.toSubgroup) ∨
    (∀ t, n⁻¹ * rankOne i (BruhatGeneration.SL2.lower t) * n ∈ B.toSubgroup)

variable {T}

/-- The remaining positive-root subgroup is normalized by the omitted simple
root subgroup. This is relative normalization, not normality in the ambient group. -/
@[expose]
public def SimpleRootRemainderNormalization (D : RootGroupData G T)
    (P : Set D.Root) : Prop :=
  ∀ α ∈ FundamentalRootsFor D P,
    (D.rootSubgroup α).toSubgroup ≤
      Subgroup.normalizer (RootSubgroupGenerated D (P \ {α}) : Set (Variety.Point G))

end Theory.AlgebraicGroup.BorelIntersectionGeometry
