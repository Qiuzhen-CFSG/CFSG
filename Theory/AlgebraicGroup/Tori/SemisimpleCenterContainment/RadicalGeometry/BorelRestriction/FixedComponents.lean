module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.CompleteModel
public import Theory.AlgebraicGroup.Variety.MorphicActionFixedLocus
public import Theory.AlgebraicGroup.Variety.GeometricComponents

/-!
# The actual fixed components for Borel restriction

Construct the reduced irreducible components of the subtorus-fixed locus in
an actual complete homogeneous model. Each is a complete closed subvariety of
the model, its points are fixed by the subtorus, and one contains the Borel
basepoint whenever the subtorus lies in the Borel.

We also specify the reduced inverse image under the actual orbit morphism.
Its connectedness, and transitivity of the centralizer on a fixed component,
are not built into these definitions. They are the remaining geometric steps
of Borel, *Linear Algebraic Groups*, §11.15.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

open BorelGeometricConjugacy Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

/-- An irreducible component of the actual fixed locus, as a closed
subvariety of the ambient complete model. -/
@[expose] public noncomputable def fixedComponent
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    ClosedSubvariety M.variety :=
  let F := M.action.subgroupFixedLocus S.toSubgroup
  let C := irreducibleComponentSubvariety F.toGeometric Z
  { toGeometric := C.toGeometric
    inclusion := C.inclusion.comp F.inclusion
    isClosedImmersion := by
      change IsClosedImmersion (C.inclusion.hom ≫ F.inclusion.hom)
      infer_instance }

/-- The fixed component carries its genuine irreducible reduced scheme. -/
public theorem fixedComponent_isIrreducible
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    IsIrreducible (fixedComponent M S Z).toGeometric := by
  change IrreducibleSpace
    (irreducibleComponentSubvariety (M.action.subgroupFixedLocus S.toSubgroup).toGeometric Z).toGeometric.toScheme
  infer_instance

/-- Every fixed component is complete as a closed subvariety of the model. -/
public theorem fixedComponent_isComplete
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    IsComplete (fixedComponent M S Z).toGeometric :=
  (fixedComponent M S Z).isComplete M.complete

/-- Points on a fixed component are fixed by every point of the subtorus. -/
public theorem fixedComponent_fixed
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (x : Point (fixedComponent M S Z).toGeometric) (s : S.toSubgroup) :
    M.action.toMulAction.smul (s : Variety.Point H) ((fixedComponent M S Z).inclusion x) =
      (fixedComponent M S Z).inclusion x :=
  M.action.subgroupFixedLocus_fixed S.toSubgroup
    ((irreducibleComponentSubvariety _ Z).inclusion x) s

/-- A subtorus contained in the Borel fixes its basepoint, which therefore
lies in some actual irreducible component of the fixed locus. -/
public theorem exists_fixedComponent_basePoint
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H) (hSB : S ≤ B) :
    ∃ (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
      (x : Point (fixedComponent M S Z).toGeometric),
      (fixedComponent M S Z).inclusion x = modelBasePoint M := by
  have hfix (s : S.toSubgroup) :
      M.action.toMulAction.smul (s : Variety.Point H) (modelBasePoint M) = modelBasePoint M :=
    (modelBasePoint_stabilizer M s).mpr (hSB s.property)
  obtain ⟨f, hf, -⟩ :=
    (M.action.point_mem_subgroupFixedLocus_iff S.toSubgroup (modelBasePoint M)).mp hfix
  let F := M.action.subgroupFixedLocus S.toSubgroup
  have hcover : f.1 (IsLocalRing.closedPoint k) ∈
      ⋃₀ irreducibleComponents F.toGeometric.toScheme := by
    rw [sUnion_irreducibleComponents]
    trivial
  obtain ⟨Z, hZ, hfZ⟩ := Set.mem_sUnion.mp hcover
  let C := irreducibleComponentSubvariety F.toGeometric ⟨Z, hZ⟩
  have hmem : f.1 (IsLocalRing.closedPoint k) ∈ Set.range C.inclusion.hom := by
    rw [irreducibleComponentSubvariety_range]
    exact hfZ
  obtain ⟨x, hx⟩ := (C.inclusion.point_mem_range_iff_closedPoint_mem_range f).mpr hmem
  refine ⟨⟨Z, hZ⟩, x, ?_⟩
  change F.inclusion ((irreducibleComponentSubvariety F.toGeometric ⟨Z, hZ⟩).inclusion x) = _
  exact (congrArg (fun y => F.inclusion y) hx).trans hf

/-- The actual complete model and a fixed component containing the Borel
basepoint exist without any extra geometric hypothesis. -/
public theorem exists_model_fixedComponent
    (S B : ClosedSubgroup H) (hB : IsBorelSubgroup B) (hSB : S ≤ B) :
    ∃ (M : CompleteModel B)
      (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
      (x : Point (fixedComponent M S Z).toGeometric),
      (fixedComponent M S Z).inclusion x = modelBasePoint M := by
  obtain ⟨M⟩ := nonempty_completeModel B hB
  obtain ⟨Z, x, hx⟩ := exists_fixedComponent_basePoint M S hSB
  exact ⟨M, Z, x, hx⟩

/-- The reduced geometric inverse image of a closed subvariety under the
actual orbit morphism based at the prescribed Borel. -/
@[expose] public noncomputable def componentPreimage
    {B : ClosedSubgroup H} (M : CompleteModel B) (X : ClosedSubvariety M.variety) :
    ClosedSubvariety (ofAffine H) :=
  reducedClosedSubvariety (ofAffine H)
    ⟨(M.action.orbitMorphismAt (modelBasePoint M)).hom ⁻¹' Set.range X.inclusion.hom,
      X.inclusion.hom.isClosedEmbedding.isClosed_range.preimage
        (M.action.orbitMorphismAt (modelBasePoint M)).hom.continuous⟩

/-- The preimage carrier has precisely the required scheme-point support. -/
public theorem componentPreimage_range
    {B : ClosedSubgroup H} (M : CompleteModel B) (X : ClosedSubvariety M.variety) :
    Set.range (componentPreimage M X).inclusion.hom =
      (M.action.orbitMorphismAt (modelBasePoint M)).hom ⁻¹' Set.range X.inclusion.hom :=
  reducedClosedSubvariety_range _ _

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
