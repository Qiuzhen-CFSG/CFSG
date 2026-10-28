module

public import Theory.AlgebraicGroup.RootData.Cocharacters

/-!
This module records the algebraic data used by the fundamental-coroot torus
parametrization and ordered root products in GLS3, Theorems 1.12.5(b) and
1.12.7.  A finite list enumerates a chosen root set.  The two coordinate-word
definitions form products of coroot or root-subgroup factors, while
`FundamentalCorootMorphism` packages the former as a regular map from a product
of multiplicative groups.

Raw `ChevalleyData` only supplies point functions.  The
`IsAlgebraicFundamentalCorootData` structure identifies those functions with
actual torus cocharacters and records their Cartan pairings and their relation
to the chosen root-system base.  Keeping this interface below the numbered
Chevalley-presentation theorems lets later torus arguments use it without
depending on unresolved presentation results.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose] public def EnumeratesRootSet {Root : Type*}
    (roots : Set Root) (order : List Root) : Prop :=
  order.Nodup ∧ ∀ alpha, alpha ∈ order ↔ alpha ∈ roots

/-- Every finite root set admits a duplicate-free list enumeration. -/
public theorem exists_enumeratesRootSet {Root : Type*} (roots : Set Root)
    [Fintype roots] : ∃ order : List Root, EnumeratesRootSet roots order := by
  classical
  let rootsFinset : Finset Root := (Set.toFinite roots).toFinset
  refine ⟨rootsFinset.toList, rootsFinset.nodup_toList, ?_⟩
  intro alpha
  simp [rootsFinset]

@[expose] public def fundamentalCorootCoordinateWord
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    (order : List D.Root) (parameters : Fin order.length → kˣ) :
    Variety.Point K :=
  (List.ofFn fun i => C.h (order.get i) (parameters i)).prod

@[expose] public def orderedChevalleyProduct
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    (order : List D.Root) (parameters : Fin order.length → k) :
    Variety.Point K :=
  (List.ofFn fun i => C.x (order.get i) (parameters i)).prod

omit [IsAlgClosed k] in
/-- Pointwise expansion of the fundamental-coroot coordinate word. -/
public theorem fundamentalCorootCoordinateWord_eq
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    (order : List D.Root) (parameters : Fin order.length → kˣ) :
    fundamentalCorootCoordinateWord C order parameters =
      (List.ofFn fun i => C.h (order.get i) (parameters i)).prod :=
  rfl

public structure FundamentalCorootMorphism
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    (order : List D.Root) where
  map : AlgebraicGroup.Morphism (dVariety k order.length) T.carrierVariety
  point_formula : ∀ x,
    T.includePoint (map.onPoints x) =
      fundamentalCorootCoordinateWord C order (dPointEquiv order.length x)

/-- The algebraic root cocharacters and based root-datum identification needed
to interpret the Chevalley functions `C.h` as fundamental coroots. -/
public structure IsAlgebraicFundamentalCorootData
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {iota R M N : Type*} [Finite iota] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing iota R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ iota)
    (base : P.Base) where
  rootCocharacter : D.Root → ClosedSubgroupTorusCocharacter T
  rootCocharacter_spec : ∀ alpha beta,
    WeightCocharacterEquation T (D.rootWeight alpha) (rootCocharacter beta)
      (P.pairingIn ℤ (e alpha) (e beta))
  simple_root_spec : ∀ alpha, alpha ∈ D.simple ↔ e alpha ∈ base.support
  h_spec : ∀ alpha (t : kˣ),
    T.includePoint
        ((rootCocharacter alpha).onPoints
          ((dPointEquiv 1).symm (fun _ => t))) = C.h alpha t

end Theory.AlgebraicGroup
