module

public import Theory.AlgebraicGroup.Borel.RootStructure.FundamentalCorootData
public import Theory.AlgebraicGroup.Cartan.Exceptional
public import Theory.AlgebraicGroup.RootData.PositiveRootCollection
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
Data interfaces for the unipotent root-product clauses of GLS3 Theorem 1.12.7.

The ordered-product set records one factor from each listed root subgroup.
`PositiveRootCombinations` is the support of a two-root Chevalley commutator,
while `ClosedRootProduct` and `NormalRootProduct` package the algebraic subgroup
realizing a closed root subset or positive-root ideal.  The three transfer
lemmas convert vector addition in a compatible root-system realization to the
partial root addition used by those predicates.

These declarations are kept below the numbered center theorems because their
mathematics uses only root data, Chevalley collection, and generated root
subgroups.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] public def OrderedRootSubgroupProductFin
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (order : List D.Root) :
    Set (Variety.Point K) :=
  {g | ∃ factors : Fin order.length → Variety.Point K,
    (∀ i, factors i ∈ D.rootSubgroup (order.get i)) ∧
      g = (List.ofFn factors).prod}

@[expose] public def PositiveRootCombinations
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type*} [Finite ι] [Field R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (e : D.Root ≃ ι)
    (alpha beta : D.Root) : Set D.Root :=
  {gamma | ∃ i j : ℕ, 0 < i ∧ 0 < j ∧
    P.root (e gamma) =
      (i : R) • P.root (e alpha) + (j : R) • P.root (e beta)}

public structure ClosedRootProduct
    {K : Variety k} [AlgebraicGroup K]
    {T U : ClosedSubgroup K} (D : RootGroupData K T)
    (roots : Set D.Root) where
  carrier : ClosedSubgroup K
  le_unipotent : carrier ≤ U
  generated : carrier.toSubgroup = RootSubgroupGenerated D roots
  every_order : ∀ order, EnumeratesRootSet roots order →
    (carrier : Set (Variety.Point K)) = OrderedRootSubgroupProductFin D order

public structure NormalRootProduct
    {K : Variety k} [AlgebraicGroup K]
    {T U : ClosedSubgroup K} (D : RootGroupData K T)
    (roots : Set D.Root) where
  carrier : ClosedSubgroup K
  le_unipotent : carrier ≤ U
  generated : carrier.toSubgroup = RootSubgroupGenerated D roots
  every_order : ∀ order, EnumeratesRootSet roots order →
    (carrier : Set (Variety.Point K)) = OrderedRootSubgroupProductFin D order
  normal_in_unipotent :
    (carrier.toSubgroup.subgroupOf U.toSubgroup).Normal

omit [IsAlgClosed k] in
/-- A positive system is closed under addition in any compatible root-system
realization. -/
public lemma IsPositiveSystem.mem_of_root_eq_add
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {e : D.Root ≃ ι}
    {positiveRoots : Set D.Root} (hPositive : IsPositiveSystem D positiveRoots)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha beta gamma : D.Root} (halpha : alpha ∈ positiveRoots)
    (hbeta : beta ∈ positiveRoots)
    (hroot : P.root (e gamma) = P.root (e alpha) + P.root (e beta)) :
    gamma ∈ positiveRoots :=
  hPositive.2.2 alpha halpha beta hbeta gamma (hAdd.add_of_root_eq_add hroot)

omit [IsAlgClosed k] in
/-- A `D.add`-closed root set contains every root which is the vector sum of
two of its roots in a compatible realization. -/
public lemma IsClosedRootSubset.mem_of_root_eq_add
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {e : D.Root ≃ ι}
    {roots : Set D.Root} (hClosed : IsClosedRootSubset D roots)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha beta gamma : D.Root} (halpha : alpha ∈ roots) (hbeta : beta ∈ roots)
    (hroot : P.root (e gamma) = P.root (e alpha) + P.root (e beta)) :
    gamma ∈ roots :=
  hClosed alpha halpha beta hbeta gamma (hAdd.add_of_root_eq_add hroot)

omit [IsAlgClosed k] in
/-- A root ideal contains every root which is the vector sum of one of its
roots and a positive root in a compatible realization. -/
public lemma IsRootIdealIn.mem_of_root_eq_add
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T}
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {e : D.Root ≃ ι}
    {positiveRoots roots : Set D.Root}
    (hIdeal : IsRootIdealIn D positiveRoots roots)
    (hAdd : IsRootAdditionRealization D P e)
    {alpha beta gamma : D.Root} (halpha : alpha ∈ roots)
    (hbeta : beta ∈ positiveRoots)
    (hroot : P.root (e gamma) = P.root (e alpha) + P.root (e beta)) :
    gamma ∈ roots :=
  hIdeal.2 alpha halpha beta hbeta gamma (hAdd.add_of_root_eq_add hroot)

end Theory.AlgebraicGroup
