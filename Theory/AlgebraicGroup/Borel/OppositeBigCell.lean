module

public import Theory.AlgebraicGroup.Borel.RootBorelDecomposition

universe u

/-!
The opposite-Borel big-cell interface for realized root data.

For a positive system `P`, `RealizedRootBorelOppositeData` records the two
compatible Borel/root witnesses and provides their exact `T * U` pointwise
decompositions.  This module adds the geometric opposite condition
`B ∩ Bopp = T` and the source big-cell conclusion that `B * Bopp` is dense.  The
density hypothesis is intentionally explicit: it is the geometric content of
GLS3, Chapter 2, (6.2)(c), while the Borel and root-decomposition fields are
the algebraic outputs of Chapter 1, Theorems 1.11.2 and 1.11.4
(`refs/KGroup/GLS3/Chapter1.tex:477-485`,
`refs/KGroup/GLS3/Chapter2St2.tex:705`).

The shared closed-subgroup product module proves that a dense product is open
by translating a nonempty open subset of its constructible multiplication
range.  Consequently this package exposes both equivalent dense/open forms
without importing the unresolved Bruhat or actual-root-generation consumers.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k]

public structure OppositeBorelBigCell
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T) (P : Set D.Root) where
  data : RealizedRootBorelOppositeData T D P
  intersection_eq_torus :
    data.B.toSubgroup ⊓ data.Bopp.toSubgroup = T.toSubgroup
  product_dense : Dense
    ((data.B.toSubgroup : Set (Variety.Point K)) *
      (data.Bopp.toSubgroup : Set (Variety.Point K)))

namespace OppositeBorelBigCell

variable {K : Variety k} [AlgebraicGroup K]
  {T : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}

/-- Assemble the opposite-Borel package from the source decomposition data,
the torus intersection, and the geometric big-cell density statement.  The
definition is exposed so consumers can reduce its structure projections. -/
@[expose]
public def of_data
    (H : RealizedRootBorelOppositeData T D P)
    (hinter : H.B.toSubgroup ⊓ H.Bopp.toSubgroup = T.toSubgroup)
    (hdense : Dense
      ((H.B.toSubgroup : Set (Variety.Point K)) *
        (H.Bopp.toSubgroup : Set (Variety.Point K)))) :
    OppositeBorelBigCell T D P :=
  { data := H
    intersection_eq_torus := hinter
    product_dense := hdense }

/-- The positive Borel contains the fixed torus. -/
public theorem torus_le_positive (H : OppositeBorelBigCell T D P) :
    T.toSubgroup ≤ H.data.B.toSubgroup := by
  rw [H.data.positive_witness.torus_unipotent_generate]
  exact le_sup_left

/-- The opposite Borel contains the fixed torus. -/
public theorem torus_le_negative (H : OppositeBorelBigCell T D P) :
    T.toSubgroup ≤ H.data.Bopp.toSubgroup := by
  rw [H.data.opposite_witness.torus_unipotent_generate]
  exact le_sup_left

/-- The positive Borel/root pointwise decomposition. -/
public theorem positive_decomposition (H : OppositeBorelBigCell T D P) :
    ∀ x, x ∈ H.data.B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u := by
  exact H.data.positive_decomposition

/-- The opposite Borel/root pointwise decomposition. -/
public theorem negative_decomposition (H : OppositeBorelBigCell T D P) :
    ∀ x, x ∈ H.data.Bopp ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D (D.neg ⁻¹' P) ∧ x = t * u := by
  exact H.data.opposite_decomposition

/-- The multiplication morphism has the opposite-Borel pointwise product as
its range. -/
public theorem product_range (H : OppositeBorelBigCell T D P) :
    ∃ m : Variety.Morphism
      (Variety.prod H.data.B.carrierVariety H.data.Bopp.carrierVariety) K,
      Set.range m.toFun =
        (H.data.B.toSubgroup : Set (Variety.Point K)) *
          (H.data.Bopp.toSubgroup : Set (Variety.Point K)) := by
  exact exists_closedSubgroup_productMorphism_range_eq_pointwise_mul
    H.data.B H.data.Bopp

/-- The dense opposite-Borel product is open. -/
public theorem product_open
    [IsAlgClosed k]
    [Nonempty (Variety.Point K)] [PreirreducibleSpace (Variety.Point K)]
    (H : OppositeBorelBigCell T D P) :
    IsOpen
      ((H.data.B.toSubgroup : Set (Variety.Point K)) *
        (H.data.Bopp.toSubgroup : Set (Variety.Point K))) := by
  exact closedSubgroup_product_isOpen_of_dense H.data.B H.data.Bopp
    H.product_dense

/-- Assemble the package when the geometric input is stated as openness.
The product contains the identity, so openness gives density in the
preirreducible ambient point space.  The definition is exposed so the stored
Borel data remains definitionally the input package across module boundaries. -/
@[expose]
public def of_open
    [Nonempty (Variety.Point K)] [PreirreducibleSpace (Variety.Point K)]
    (H : RealizedRootBorelOppositeData T D P)
    (hinter : H.B.toSubgroup ⊓ H.Bopp.toSubgroup = T.toSubgroup)
    (hopen : IsOpen
      ((H.B.toSubgroup : Set (Variety.Point K)) *
        (H.Bopp.toSubgroup : Set (Variety.Point K)))) :
    OppositeBorelBigCell T D P :=
  of_data H hinter <| hopen.dense <|
    ⟨1, by simpa using Set.mul_mem_mul H.B.one_mem H.Bopp.one_mem⟩

/-- Open big-cell generation of the torus and all realized root subgroups. -/
public theorem generated_eq_top_of_open
    [IsAlgClosed k]
    (H : OppositeBorelBigCell T D P)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    [Nonempty (Variety.Point K)] [PreirreducibleSpace (Variety.Point K)] :
    RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤ := by
  exact H.data.generated_eq_top_of_open hK H.product_open

/-- Dense big-cell generation of the torus and all realized root subgroups. -/
public theorem generated_eq_top_of_dense
    [IsAlgClosed k]
    [Nonempty (Variety.Point K)] [PreirreducibleSpace (Variety.Point K)]
    (H : OppositeBorelBigCell T D P)
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K))) :
    RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤ := by
  exact H.data.generated_eq_top_of_dense hK H.product_dense

end OppositeBorelBigCell

end Theory.AlgebraicGroup
