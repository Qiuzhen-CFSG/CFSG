module

public import Theory.Mathieu.M23.QuasithinGeometry.Design
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Stabilizers
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image

/-!
# The M23 pair stabilizer and its field plane

The complementary points and the heptads through the deleted pair, with that
pair removed, are explicitly coordinatized as the points and lines of PG(2,4).
Their natural M23 actions identify the setwise pair stabilizer with the actual
semidirect product PSL(3,4) ⋊ C₂, where C₂ acts by entrywise Frobenius. The
pointwise pair stabilizer corresponds to PSL(3,4). The inclusion in the full
PΓL(3,4) has index three.

The equivalences are constructed from the equal faithful collineation images
proved in `PairPlane.Image`. The intrinsic intersection descriptions in
`PairPlane.Stabilizers` then identify the adjacent-pair intersection with the
PSL point parabolic and the pair/heptad intersection with the extension's line
stabilizer. The selected point lies on the selected line, and all subgroup
maps commute with the same ambient pair equivalence.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 5.2.18(1–2), printed p.655 (PDF p.672); the compatible parabolics are
used in 5.2.20, printed p.656. See also Aschbacher, *Sporadic Groups*, §18.
-/

@[expose] public section

open Configuration
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.PairPlane
open Matrix.PSL3Four

/-- Incidence coordinates on the actual complementary points, adjusted so that
Frobenius belongs to the pair-stabilizer image. -/
noncomputable abbrev pointEquiv : pairComplement x.val ≃ PG := PairPlaneImage.pointEquiv

/-- The compatible dual coordinates on the actual derived lines. -/
noncomputable abbrev lineEquiv : pairLines x.val ≃ PG := PairPlaneImage.lineEquiv

/-- The derived design has exactly the orthogonality incidence of PG(2,4). -/
theorem incident_iff (p : pairComplement x.val) (l : pairLines x.val) :
    pointEquiv p ∈ lineEquiv l ↔ p.val ∈ l.val := PairPlaneImage.incident_iff p l

/-- The actual M23 pair stabilizer is PSL(3,4) extended by Frobenius.
The equivalence is obtained from their equal faithful collineation images. -/
noncomputable def pairEquiv : pairStabilizer ≃* FieldExtension :=
  (MonoidHom.ofInjective PairPlaneImage.collineation_injective).trans
    ((MulEquiv.subgroupCongr PairPlaneImage.collineation_range).trans
      (MonoidHom.ofInjective pairedAction_injective).symm)

@[simp] theorem pairEquiv_collineation (g : pairStabilizer) :
    pairedAction (pairEquiv g) = PairPlaneImage.collineation g := by
  simp [pairEquiv, MonoidHom.ofInjective_apply]

/-- Fixing both deleted points corresponds precisely to the linear PSL subgroup. -/
noncomputable def pointwiseEquiv : pointwisePairStabilizer ≃* PSL :=
  (MonoidHom.ofInjective PairPlaneImage.pointwiseCollineation_injective).trans
    ((MulEquiv.subgroupCongr PairPlaneImage.pointwiseCollineation_range).trans
      (MonoidHom.ofInjective pslCollineation_injective).symm)

@[simp] theorem pointwiseEquiv_collineation (g : pointwisePairStabilizer) :
    pslCollineation (pointwiseEquiv g) = PairPlaneImage.collineation g.val := by
  simp [pointwiseEquiv, MonoidHom.ofInjective_apply]
  rfl

@[simp] theorem pairEquiv_pointwise (g : pointwisePairStabilizer) :
    pairEquiv g.val = linearInclusion (pointwiseEquiv g) := by
  apply pairedAction_injective
  rw [pairEquiv_collineation, pairedAction_linearInclusion, pointwiseEquiv_collineation]

@[simp] theorem pairEquiv_point (g : pairStabilizer) (p : pairComplement x.val) :
    pointAction (pairEquiv g) (PairPlaneImage.pointEquiv p) =
      PairPlaneImage.pointEquiv (complementAction x.val g p) := by
  change Collineation.pointHom PG PG (pairedAction (pairEquiv g)) _ = _
  rw [pairEquiv_collineation, PairPlaneImage.collineation_point]

@[simp] theorem pairEquiv_line (g : pairStabilizer) (l : pairLines x.val) :
    Matrix.PSL3Four.lineAction (pairEquiv g) (PairPlaneImage.lineEquiv l) =
      PairPlaneImage.lineEquiv (M23Geometry.lineAction x.val g l) := by
  change Collineation.lineHom PG PG (pairedAction (pairEquiv g)) _ = _
  rw [pairEquiv_collineation, PairPlaneImage.collineation_line]

@[simp] theorem pointwiseEquiv_point (g : pointwisePairStabilizer)
    (p : pairComplement x.val) :
    pointwiseEquiv g • PairPlaneImage.pointEquiv p =
      PairPlaneImage.pointEquiv (complementAction x.val g.val p) := by
  rw [← pslCollineation_point, pointwiseEquiv_collineation,
    PairPlaneImage.collineation_point]

/-- Fixing the deleted pair pointwise is equivalent to a trivial field component. -/
theorem mem_pointwise_iff (g : pairStabilizer) :
    g ∈ pointwisePairStabilizer ↔ fieldProjection (pairEquiv g) = 1 := by
  constructor
  · intro hg
    rw [pairEquiv_pointwise ⟨g, hg⟩, fieldProjection_linearInclusion]
  · intro hg
    have hm : pairEquiv g ∈ linearInclusion.range := by
      rw [range_linearInclusion]
      exact hg
    obtain ⟨a, ha⟩ := hm
    obtain ⟨h, rfl⟩ := pointwiseEquiv.surjective a
    have hh : h.val = g := pairEquiv.injective ((pairEquiv_pointwise h).trans ha)
    exact hh ▸ h.property

@[simp] theorem pairEquiv_frobenius :
    pairEquiv PairPlaneImage.frobeniusLift =
      fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)) := by
  apply pairedAction_injective
  rw [pairEquiv_collineation, pairedAction_field_generator]
  exact PairPlaneImage.frobeniusLift_collineation

/-- The point on the field plane corresponding to the adjacent pair. -/
noncomputable def planePoint : PG := PairPlaneImage.pointEquiv adjacentPoint

/-- The line on the field plane corresponding to the distinguished heptad. -/
noncomputable def planeLine : PG := PairPlaneImage.lineEquiv omegaLine

theorem planePoint_mem_planeLine : planePoint ∈ planeLine :=
  (PairPlaneImage.incident_iff _ _).mpr adjacentPoint_mem_omegaLine

/-- The point parabolic in the actual determinant-one projective group. -/
noncomputable def pointParabolic : Subgroup PSL := MulAction.stabilizer PSL planePoint

/-- The line stabilizer in the extension by Frobenius. -/
noncomputable def lineStabilizer : Subgroup FieldExtension :=
  (MulAction.stabilizer (Equiv.Perm PG) planeLine).comap Matrix.PSL3Four.lineAction

/-- Inclusion of the coordinate PSL group into the actual M23 group. -/
noncomputable def pslToM23 : PSL →* M23 :=
  pairStabilizer.subtype.comp
    (pointwisePairStabilizer.subtype.comp pointwiseEquiv.symm.toMonoidHom)

theorem pslToM23_injective : Function.Injective pslToM23 :=
  Subtype.val_injective.comp (Subtype.val_injective.comp pointwiseEquiv.symm.injective)

/-- The coordinate extension embedded in M23, with its original pair action. -/
noncomputable def fieldExtensionToM23 : FieldExtension →* M23 :=
  pairStabilizer.subtype.comp pairEquiv.symm.toMonoidHom

theorem fieldExtensionToM23_injective : Function.Injective fieldExtensionToM23 :=
  Subtype.val_injective.comp pairEquiv.symm.injective

@[simp] theorem fieldExtensionToM23_linear (a : PSL) :
    fieldExtensionToM23 (linearInclusion a) = pslToM23 a := by
  have h := pairEquiv_pointwise (pointwiseEquiv.symm a)
  rw [pointwiseEquiv.apply_symm_apply] at h
  change (pairEquiv.symm (linearInclusion a)).val = (pointwiseEquiv.symm a).val.val
  rw [← h, pairEquiv.symm_apply_apply]

/-- The point parabolic maps onto the intersection of the two adjacent-pair
stabilizers in M23. -/
theorem pointParabolic_map : pointParabolic.map pslToM23 =
    pairStabilizer ⊓ MulAction.stabilizer M23 y.val := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    let h := pointwiseEquiv.symm a
    refine ⟨h.val.property, (mem_adjacent_stabilizer_iff h.val).mpr ⟨h.property, ?_⟩⟩
    apply PairPlaneImage.pointEquiv.injective
    rw [← pointwiseEquiv_point]
    change pointwiseEquiv (pointwiseEquiv.symm a) • planePoint = planePoint
    rw [pointwiseEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨hx, hy⟩
    let g' : pairStabilizer := ⟨g, hx⟩
    have hg := (mem_adjacent_stabilizer_iff g').mp hy
    let h : pointwisePairStabilizer := ⟨g', hg.1⟩
    refine ⟨pointwiseEquiv h, ?_, ?_⟩
    · change pointwiseEquiv h • PairPlaneImage.pointEquiv adjacentPoint = _
      rw [pointwiseEquiv_point, hg.2]
      rfl
    · change (pointwiseEquiv.symm (pointwiseEquiv h)).val.val = g
      rw [pointwiseEquiv.symm_apply_apply]

/-- The line stabilizer maps onto the intersection of the pair and heptad
stabilizers in M23. -/
theorem lineStabilizer_map : lineStabilizer.map fieldExtensionToM23 =
    pairStabilizer ⊓ heptadStabilizer := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    let h := pairEquiv.symm a
    refine ⟨h.property, (mem_heptadStabilizer_iff h).mpr ?_⟩
    apply PairPlaneImage.lineEquiv.injective
    rw [← pairEquiv_line]
    change Matrix.PSL3Four.lineAction (pairEquiv (pairEquiv.symm a)) planeLine = planeLine
    rw [pairEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨hx, hy⟩
    let h : pairStabilizer := ⟨g, hx⟩
    have hh := (mem_heptadStabilizer_iff h).mp hy
    refine ⟨pairEquiv h, ?_, ?_⟩
    · change Matrix.PSL3Four.lineAction (pairEquiv h)
        (PairPlaneImage.lineEquiv omegaLine) = _
      rw [pairEquiv_line, hh]
      rfl
    · change (pairEquiv.symm (pairEquiv h)).val = g
      rw [pairEquiv.symm_apply_apply]

/-- The adjacent-pair intersection is the corresponding PSL point parabolic. -/
noncomputable def adjacentEquiv :
    ↥(pairStabilizer ⊓ MulAction.stabilizer M23 y.val) ≃* pointParabolic :=
  ((pointParabolic.equivMapOfInjective pslToM23 pslToM23_injective).trans
    (MulEquiv.subgroupCongr pointParabolic_map)).symm

/-- The pair/heptad intersection is the field-plane line stabilizer. -/
noncomputable def heptadEquiv :
    ↥(pairStabilizer ⊓ heptadStabilizer) ≃* lineStabilizer :=
  ((lineStabilizer.equivMapOfInjective fieldExtensionToM23 fieldExtensionToM23_injective).trans
    (MulEquiv.subgroupCongr lineStabilizer_map)).symm

@[simp] theorem adjacentEquiv_symm_coe (a : pointParabolic) :
    (adjacentEquiv.symm a).val = pslToM23 a.val := rfl

@[simp] theorem heptadEquiv_symm_coe (a : lineStabilizer) :
    (heptadEquiv.symm a).val = fieldExtensionToM23 a.val := rfl

/-- Compatibility of the parabolic identification with the ambient embedding. -/
@[simp] theorem adjacentEquiv_coe
    (g : ↥(pairStabilizer ⊓ MulAction.stabilizer M23 y.val)) :
    pslToM23 (adjacentEquiv g).val = g.val := by
  rw [← adjacentEquiv_symm_coe, adjacentEquiv.symm_apply_apply]

/-- Compatibility of the line identification with the ambient embedding. -/
@[simp] theorem heptadEquiv_coe (g : ↥(pairStabilizer ⊓ heptadStabilizer)) :
    fieldExtensionToM23 (heptadEquiv g).val = g.val := by
  rw [← heptadEquiv_symm_coe, heptadEquiv.symm_apply_apply]

/-- The natural inclusion of the pair stabilizer into the full projective
semilinear group. -/
noncomputable def pairToPGammaL : pairStabilizer →* PGammaL :=
  fieldExtensionToPGammaL.comp pairEquiv.toMonoidHom

theorem pairToPGammaL_injective : Function.Injective pairToPGammaL :=
  fieldExtensionToPGammaL_injective.comp pairEquiv.injective

/-- This is the index-three field extension, distinguished from the full
projective semilinear group of order 120960. -/
theorem pairToPGammaL_range_index : pairToPGammaL.range.index = 3 := by
  have h : pairToPGammaL.range = fieldExtensionToPGammaL.range := by
    rw [pairToPGammaL, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr pairEquiv.surjective, ← MonoidHom.range_eq_map]
  rw [h, fieldExtensionToPGammaL_range_index]

/-- The pointwise pair subgroup corresponds to the linear kernel. -/
theorem pointwise_comap_fieldKernel :
    fieldProjection.ker.comap pairEquiv.toMonoidHom = pointwisePairStabilizer := by
  ext g
  exact (mem_pointwise_iff g).symm

theorem pointwise_map_linear :
    pointwisePairStabilizer.map pairEquiv.toMonoidHom = linearInclusion.range := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨pointwiseEquiv ⟨g, hg⟩, (pairEquiv_pointwise ⟨g, hg⟩).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨(pointwiseEquiv.symm b).val, (pointwiseEquiv.symm b).property,
      by
        change pairEquiv (pointwiseEquiv.symm b).val = linearInclusion b
        rw [pairEquiv_pointwise, pointwiseEquiv.apply_symm_apply]⟩

/-- The adjacent-parabolic map is the restriction of the pair equivalence,
followed by the standard inclusion of PSL into its field extension. -/
theorem pairEquiv_adjacent
    (g : ↥(pairStabilizer ⊓ MulAction.stabilizer M23 y.val)) :
    pairEquiv ⟨g.val, g.property.1⟩ = linearInclusion (adjacentEquiv g).val := by
  apply fieldExtensionToM23_injective
  rw [fieldExtensionToM23_linear, adjacentEquiv_coe]
  change (pairEquiv.symm (pairEquiv _)).val = g.val
  rw [pairEquiv.symm_apply_apply]

/-- The heptad/line-stabilizer map is the restriction of the same pair equivalence. -/
theorem pairEquiv_heptad (g : ↥(pairStabilizer ⊓ heptadStabilizer)) :
    pairEquiv ⟨g.val, g.property.1⟩ = (heptadEquiv g).val := by
  apply fieldExtensionToM23_injective
  rw [heptadEquiv_coe]
  change (pairEquiv.symm (pairEquiv _)).val = g.val
  rw [pairEquiv.symm_apply_apply]

end Sporadic.Mathieu.M23Geometry.PairPlane
