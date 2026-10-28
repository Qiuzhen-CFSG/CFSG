module

public import Theory.AlgebraicGroup.Borel.IsogenyImage
public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs

universe u

/-!
Bridge realized root data to the pointwise Borel decompositions used by the
root-generation arguments.  A witness
`IsBorelOfPositiveSystem D P B` already contains the radical and its root
generation equality; its normality inside `B`, together with the torus factor,
turns that subgroup equality into the required pointwise `T * U(P)` formula.

The existence of compatible positive and opposite Borel witnesses, and the
openness or density of their product (the big-cell input), remain explicit
hypotheses.  This module therefore supplies only the geometric-to-algebraic
bridge and does not use the derived-group generation theorem as an assumption.
The data and decomposition fields follow GLS3, Theorems 1.10.1(a) and
1.11.2, `refs/KGroup/GLS3/Chapter1.tex:411-414,477`.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

section

variable {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}

omit [IsAlgClosed k] in
private lemma closedSubgroup_pointwise_decomposition
    (B T U : ClosedSubgroup K)
    (hsup : T.toSubgroup ⊔ U.toSubgroup = B.toSubgroup)
    (hnormal : T.toSubgroup ≤ Subgroup.normalizer U.toSubgroup) :
    ∀ x, x ∈ B.toSubgroup ↔ ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u := by
  have hset : (B.toSubgroup : Set (Variety.Point K)) =
      (T.toSubgroup : Set (Variety.Point K)) *
        (U.toSubgroup : Set (Variety.Point K)) := by
    calc
      (B.toSubgroup : Set (Variety.Point K)) =
          (T.toSubgroup ⊔ U.toSubgroup : Subgroup (Variety.Point K)) :=
        congrArg (fun H : Subgroup (Variety.Point K) =>
          (H : Set (Variety.Point K))) hsup.symm
      _ = (T.toSubgroup : Set (Variety.Point K)) *
          (U.toSubgroup : Set (Variety.Point K)) :=
        Subgroup.coe_mul_of_left_le_normalizer_right
          T.toSubgroup U.toSubgroup hnormal
  intro x
  change x ∈ (B.toSubgroup : Set (Variety.Point K)) ↔ _
  rw [hset]
  constructor
  · intro hx
    rcases Set.mem_mul.mp hx with ⟨t, ht, u, hu, htu⟩
    exact ⟨t, u, ht, hu, htu.symm⟩
  · rintro ⟨t, u, ht, hu, rfl⟩
    exact Set.mul_mem_mul ht hu

omit [IsAlgClosed k] in
private lemma BorelOfPositiveSystem.torus_normalizes_unipotent
    {P : Set D.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem D P B) :
    T.toSubgroup ≤ Subgroup.normalizer hB.unipotent.toSubgroup := by
  apply (Subgroup.le_normalizer_iff).2
  intro t ht u hu
  have htB : t ∈ B.toSubgroup := by
    rw [hB.torus_unipotent_generate]
    exact Subgroup.mem_sup_left ht
  exact hB.radical.2.2.1 t htB u hu

omit [IsAlgClosed k] in
/-- A Borel/root witness gives the exact pointwise decomposition consumed by
the open- and dense-product generation lemmas. -/
public theorem BorelOfPositiveSystem.pointwise_decomposition
    {P : Set D.Root} {B : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem D P B) :
    ∀ x, x ∈ B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u := by
  have hsup : T.toSubgroup ⊔ hB.unipotent.toSubgroup = B.toSubgroup :=
    hB.torus_unipotent_generate.symm
  have hdecomp := closedSubgroup_pointwise_decomposition B T hB.unipotent hsup
    (BorelOfPositiveSystem.torus_normalizes_unipotent hB)
  intro x
  constructor
  · intro hx
    have hx' : x ∈ B.toSubgroup := hx
    obtain ⟨t, u, ht, hu, hxu⟩ := (hdecomp x).mp hx'
    have ht' : t ∈ T := ht
    refine ⟨t, u, ht', ?_, hxu⟩
    rw [← hB.root_generated]
    exact hu
  · rintro ⟨t, u, ht, hu, hxu⟩
    have ht' : t ∈ T.toSubgroup := ht
    have hu' : u ∈ hB.unipotent.toSubgroup := by
      rw [hB.root_generated]
      exact hu
    apply (hdecomp x).mpr
    exact ⟨t, u, ht', hu', hxu⟩

/-- The two compatible Borel witnesses and their positive system, before the
topological big-cell hypothesis is supplied. -/
public structure RealizedRootBorelOppositeData
    (T : ClosedSubgroup K) (D : RootGroupData K T)
    (P : Set D.Root) where
  positive : IsPositiveSystem D P
  B : ClosedSubgroup K
  Bopp : ClosedSubgroup K
  B_isBorel : IsBorelSubgroup B
  Bopp_isBorel : IsBorelSubgroup Bopp
  positive_witness : IsBorelOfPositiveSystem D P B
  opposite_witness : IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp

namespace RealizedRootBorelOppositeData

variable {P : Set D.Root}

/-- Package the two witnesses without hiding the positive-system input. -/
public def of_witnesses
    (hP : IsPositiveSystem D P)
    {B Bopp : ClosedSubgroup K}
    (hB : IsBorelOfPositiveSystem D P B)
    (hBopp : IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp) :
    RealizedRootBorelOppositeData T D P :=
  { positive := hP
    B := B
    Bopp := Bopp
    B_isBorel := hB.borel
    Bopp_isBorel := hBopp.borel
    positive_witness := hB
    opposite_witness := hBopp }

omit [IsAlgClosed k] in
/-- Existential form of `of_witnesses`, useful when Borel classification
returns `Nonempty` witnesses. -/
public theorem exists_of_witnesses
    (hP : IsPositiveSystem D P)
    (hB : ∃ B : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D P B))
    (hBopp : ∃ Bopp : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) Bopp)) :
    Nonempty (RealizedRootBorelOppositeData T D P) := by
  obtain ⟨B, ⟨hB⟩⟩ := hB
  obtain ⟨Bopp, ⟨hBopp⟩⟩ := hBopp
  exact ⟨of_witnesses hP hB hBopp⟩

variable (H : RealizedRootBorelOppositeData T D P)

omit [IsAlgClosed k] in
public theorem positive_decomposition :
    ∀ x, x ∈ H.B ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D P ∧ x = t * u := by
  exact BorelOfPositiveSystem.pointwise_decomposition H.positive_witness

omit [IsAlgClosed k] in
public theorem opposite_decomposition :
    ∀ x, x ∈ H.Bopp ↔ ∃ t u,
      t ∈ T ∧ u ∈ RootSubgroupGenerated D (D.neg ⁻¹' P) ∧ x = t * u := by
  exact BorelOfPositiveSystem.pointwise_decomposition H.opposite_witness

omit [IsAlgClosed k] in
/-- Open big-cell input upgraded to the exact torus-plus-all-roots
generation equality. -/
public theorem generated_eq_top_of_open
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (hopen : IsOpen
      ((H.B.toSubgroup : Set (Variety.Point K)) *
        (H.Bopp.toSubgroup : Set (Variety.Point K)))) :
    RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤ := by
  exact rootSubgroupGenerated_sup_torus_eq_top_of_open_decomposition_product
    T H.B H.Bopp D P (D.neg ⁻¹' P) hK H.positive_decomposition
    H.opposite_decomposition hopen

/-- Dense big-cell input upgraded to the exact torus-plus-all-roots
generation equality. -/
public theorem generated_eq_top_of_dense
    [Nonempty (Variety.Point K)] [PreirreducibleSpace (Variety.Point K)]
    (hK : _root_.IsConnected (Set.univ : Set (Variety.Point K)))
    (hdense : Dense
      ((H.B.toSubgroup : Set (Variety.Point K)) *
        (H.Bopp.toSubgroup : Set (Variety.Point K)))) :
    RootSubgroupGenerated D Set.univ ⊔ T.toSubgroup = ⊤ := by
  exact rootSubgroupGenerated_sup_torus_eq_top_of_dense_opposite_decomposition_product
    T H.B H.Bopp D P H.positive hK H.positive_decomposition
    H.opposite_decomposition hdense

end RealizedRootBorelOppositeData

end

end Theory.AlgebraicGroup
