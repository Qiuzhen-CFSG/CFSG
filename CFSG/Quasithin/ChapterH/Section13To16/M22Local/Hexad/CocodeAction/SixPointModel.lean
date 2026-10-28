module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad

/-!
# Six-coordinate identification in the M22 clause of H.15.2(2)

These equivalences retain the actual inner and outer cocode actions, both
quotient maps, the six literal coordinates, and the relative intrinsic
kernels. Their inputs are the earlier M24 scalar fixed-space facts and H.14
restriction facts. They do not assume an M22 module identification.

The native quotient representations are identified with the six-coordinate
A6 and S6 deleted modules, with faithful actions and the actual quotient-map
equations. Their perfect pairing with the five-dimensional orthogonal pair
perpendicular is contragredient. The quadratic form is on that perpendicular,
and the cocode space is its dual; it does not descend through the nonsingular
pair line. This completes the module-identification branch under the permitted
earlier M24 and H.14 inputs; the parent owns the remaining H.15.2 clauses.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open MathieuCode MathieuCode.Hexad Representation.BinaryOffender
open Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.CocodeAction.SixPointModel

abbrev Model := MathieuCode.Hexad.CocodeAction.SixPointModel.H
abbrev OuterFixed := fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)
abbrev InnerFixed := fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)

/-- Six-coordinate restriction identifies the actual outer common fixed space. -/
def outerEquiv (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    OuterFixed ≃ₗ[ZMod 2] BinaryPermutation.Deleted Model :=
  MathieuCode.Hexad.CocodeAction.SixPointModel.fixedEquiv
    (f := MonoidHom.id m22PairStabilizer) (K := m22OuterHexadKernel m22SourceOctad)
    h h24.displacement h24.fixed_finrank

/-- The native inner group has the same coordinate model, with its own action. -/
def innerEquiv (h : InnerRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    InnerFixed ≃ₗ[ZMod 2] BinaryPermutation.Deleted Model :=
  MathieuCode.Hexad.CocodeAction.SixPointModel.fixedEquiv h h24.displacement h24.fixed_finrank

open MathieuCode.Hexad.CocodeAction.SixPointModel in
/-- Equivariance for the setwise pair group, before any abstract group recognition. -/
theorem outerEquiv_equivariant (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad) (g : m22OuterHexadStabilizer m22SourceOctad)
    (v : OuterFixed) :
    outerEquiv h h24 ⟨m22OuterCocodeRepresentation g.val v.val,
        fixedSpace_invariant h h24.displacement h24.fixed_finrank g v.property⟩ =
      BinaryPermutation.deletedRepresentation Model (outerCoordinateAction g) (outerEquiv h h24 v) :=
  fixedEquiv_equivariant h h24.displacement h24.fixed_finrank g v

open MathieuCode.Hexad.CocodeAction.SixPointModel in
/-- Equivariance uses the actual native M22 embedding. -/
theorem innerEquiv_equivariant (h : InnerRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad) (g : m22InnerHexadStabilizer m22SourceOctad)
    (v : InnerFixed) :
    innerEquiv h h24 ⟨m22CocodeRepresentation g.val v.val,
        fixedSpace_invariant h h24.displacement h24.fixed_finrank g v.property⟩ =
      BinaryPermutation.deletedRepresentation Model (innerCoordinateAction g) (innerEquiv h h24 v) :=
  fixedEquiv_equivariant h h24.displacement h24.fixed_finrank g v

open MathieuCode.Hexad.CocodeAction.SixPointModel in
/-- The coordinate actions have their genuine relative kernels in both cases. -/
theorem relative_kernels (hi : InnerRestrictionInput m22SourceOctad)
    (ho : OuterRestrictionInput m22SourceOctad) :
    innerCoordinateAction.ker =
      (m22InnerHexadKernel m22SourceOctad).subgroupOf (m22InnerHexadStabilizer m22SourceOctad) ∧
    outerCoordinateAction.ker =
      (m22OuterHexadKernel m22SourceOctad).subgroupOf (m22OuterHexadStabilizer m22SourceOctad) :=
  ⟨coordinateAction_ker hi.injective hi.kernel_image,
    coordinateAction_ker ho.injective ho.kernel_image⟩

open MathieuCode.Hexad.CocodeAction.SixPointModel

/-- The source inner quotient is taken inside the actual hexad stabilizer. -/
abbrev InnerQuotient := m22InnerHexadStabilizer O ⧸ pCore 2 (m22InnerHexadStabilizer O)

/-- The source outer quotient uses the setwise-pair stabilizer. -/
abbrev OuterQuotient := m22OuterHexadStabilizer O ⧸ pCore 2 (m22OuterHexadStabilizer O)

/-- The native inner quotient acts as A6 on the literal six coordinates. -/
def innerGroupEquiv (h : InnerRestrictionInput O) : InnerQuotient ≃* alternatingGroup Model :=
  innerIntrinsicQuotientAlternatingEquiv h.kernel_image

/-- The native outer quotient acts as S6 on the same coordinates. -/
def outerGroupEquiv (h : OuterRestrictionInput O) : OuterQuotient ≃* Equiv.Perm Model :=
  outerIntrinsicQuotientSymmetricEquiv h.kernel_image

@[simp] theorem innerGroupEquiv_mk (h : InnerRestrictionInput O)
    (g : m22InnerHexadStabilizer O) :
    (innerGroupEquiv h (QuotientGroup.mk g) : Equiv.Perm Model) = innerCoordinateAction g :=
  innerIntrinsicQuotientAlternatingEquiv_mk h.kernel_image g

@[simp] theorem outerGroupEquiv_mk (h : OuterRestrictionInput O)
    (g : m22OuterHexadStabilizer O) :
    outerGroupEquiv h (QuotientGroup.mk g) = outerCoordinateAction g :=
  outerIntrinsicQuotientSymmetricEquiv_mk h.kernel_image g

/-- Descent of the native inner cocode action on its common fixed space. -/
def innerQuotientRepresentation (h : InnerRestrictionInput O) (h24 : AmbientFixedInput O) :
    Representation (ZMod 2) InnerQuotient InnerFixed :=
  @quotientFixedRepresentation _ _ m22ToPairStabilizer (m22InnerHexadKernel O)
    h h24.displacement h24.fixed_finrank
    (pCore 2 (m22InnerHexadStabilizer O)) pCore_normal innerHexadKernel_subgroupOf.symm

/-- Descent of the actual setwise-pair cocode action. -/
def outerQuotientRepresentation (h : OuterRestrictionInput O) (h24 : AmbientFixedInput O) :
    Representation (ZMod 2) OuterQuotient OuterFixed :=
  @quotientFixedRepresentation _ _ (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel O)
    h h24.displacement h24.fixed_finrank
    (pCore 2 (m22OuterHexadStabilizer O)) pCore_normal outerHexadKernel_subgroupOf.symm

@[simp] theorem innerQuotientRepresentation_mk (h : InnerRestrictionInput O)
    (h24 : AmbientFixedInput O) (g : m22InnerHexadStabilizer O) (v : InnerFixed) :
    (innerQuotientRepresentation h h24 (QuotientGroup.mk g) v).val =
      m22CocodeRepresentation g.val v.val := rfl

@[simp] theorem outerQuotientRepresentation_mk (h : OuterRestrictionInput O)
    (h24 : AmbientFixedInput O) (g : m22OuterHexadStabilizer O) (v : OuterFixed) :
    (outerQuotientRepresentation h h24 (QuotientGroup.mk g) v).val =
      m22OuterCocodeRepresentation g.val v.val := rfl

/-- The explicit restriction equivalence respects the genuine A6 quotient map. -/
theorem innerEquiv_quotient_equivariant (h : InnerRestrictionInput O)
    (h24 : AmbientFixedInput O) (q : InnerQuotient) (v : InnerFixed) :
    innerEquiv h h24 (innerQuotientRepresentation h h24 q v) =
      BinaryPermutation.deletedRepresentation Model (innerGroupEquiv h q).val
        (innerEquiv h h24 v) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (m22InnerHexadStabilizer O)) q
  change innerEquiv h h24 (innerQuotientRepresentation h h24 (QuotientGroup.mk g) v) =
    BinaryPermutation.deletedRepresentation Model (innerGroupEquiv h (QuotientGroup.mk g)).val
      (innerEquiv h h24 v)
  rw [innerGroupEquiv_mk]
  exact innerEquiv_equivariant h h24 g v

/-- The same linear identification respects the genuine S6 quotient map. -/
theorem outerEquiv_quotient_equivariant (h : OuterRestrictionInput O)
    (h24 : AmbientFixedInput O) (q : OuterQuotient) (v : OuterFixed) :
    outerEquiv h h24 (outerQuotientRepresentation h h24 q v) =
      BinaryPermutation.deletedRepresentation Model (outerGroupEquiv h q)
        (outerEquiv h h24 v) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (m22OuterHexadStabilizer O)) q
  change outerEquiv h h24 (outerQuotientRepresentation h h24 (QuotientGroup.mk g) v) =
    BinaryPermutation.deletedRepresentation Model (outerGroupEquiv h (QuotientGroup.mk g))
      (outerEquiv h h24 v)
  rw [outerGroupEquiv_mk]
  exact outerEquiv_equivariant h h24 g v

/-- Identification as representations, retaining the actual inner group quotient. -/
def innerModuleEquiv (h : InnerRestrictionInput O) (h24 : AmbientFixedInput O) :
    (innerQuotientRepresentation h h24).Equiv
      ((BinaryPermutation.deletedRepresentation Model).comp
        ((alternatingGroup Model).subtype.comp (innerGroupEquiv h).toMonoidHom)) :=
  .mk (innerEquiv h h24) (fun q => LinearMap.ext (innerEquiv_quotient_equivariant h h24 q))

/-- Identification as representations, retaining the actual outer group quotient. -/
def outerModuleEquiv (h : OuterRestrictionInput O) (h24 : AmbientFixedInput O) :
    (outerQuotientRepresentation h h24).Equiv
      ((BinaryPermutation.deletedRepresentation Model).comp (outerGroupEquiv h).toMonoidHom) :=
  .mk (outerEquiv h h24) (fun q => LinearMap.ext (outerEquiv_quotient_equivariant h h24 q))

theorem innerQuotientRepresentation_injective (h : InnerRestrictionInput O)
    (h24 : AmbientFixedInput O) : Function.Injective (innerQuotientRepresentation h h24) :=
  @quotientFixedRepresentation_injective _ _ m22ToPairStabilizer (m22InnerHexadKernel O)
    h h24.displacement h24.fixed_finrank
    (pCore 2 (m22InnerHexadStabilizer O)) pCore_normal innerHexadKernel_subgroupOf.symm

theorem outerQuotientRepresentation_injective (h : OuterRestrictionInput O)
    (h24 : AmbientFixedInput O) : Function.Injective (outerQuotientRepresentation h h24) :=
  @quotientFixedRepresentation_injective _ _ (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel O)
    h h24.displacement h24.fixed_finrank
    (pCore 2 (m22OuterHexadStabilizer O)) pCore_normal outerHexadKernel_subgroupOf.symm

/-- The model has six coordinates, and the native inner fixed space has rank five. -/
theorem inner_dimensions (h : InnerRestrictionInput O) (h24 : AmbientFixedInput O) :
    Fintype.card Model = 6 ∧ Module.finrank (ZMod 2) InnerFixed = 5 :=
  ⟨card_H, fixedSpace_finrank_five h h24.displacement h24.fixed_finrank⟩

theorem outer_dimensions (h : OuterRestrictionInput O) (h24 : AmbientFixedInput O) :
    Fintype.card Model = 6 ∧ Module.finrank (ZMod 2) OuterFixed = 5 :=
  ⟨card_H, fixedSpace_finrank_five
    (f := MonoidHom.id m22PairStabilizer) (K := m22OuterHexadKernel O)
    h h24.displacement h24.fixed_finrank⟩

/-- On every supported even octad word, the model is literal coordinate restriction
through the ambient cocode map followed by the native pair-line quotient. -/
theorem innerEquiv_apply (h : InnerRestrictionInput O) (h24 : AmbientFixedInput O)
    (v : BinaryPermutation.core O.val) :
    innerEquiv h h24
      ⟨m22PairLine.mkQ (CocodeOctad.toCocode O.val v),
        imageSpace_le_fixed h.kernel_image (LinearMap.mem_range_self toM22 v)⟩ =
      (BinaryPermutation.constants Model).mkQ (restrict v) :=
  fixedEquiv_apply h h24.displacement h24.fixed_finrank v

theorem outerEquiv_apply (h : OuterRestrictionInput O) (h24 : AmbientFixedInput O)
    (v : BinaryPermutation.core O.val) :
    outerEquiv h h24
      ⟨m22PairLine.mkQ (CocodeOctad.toCocode O.val v),
        imageSpace_le_fixed h.kernel_image (LinearMap.mem_range_self toM22 v)⟩ =
      (BinaryPermutation.constants Model).mkQ (restrict v) :=
  fixedEquiv_apply h h24.displacement h24.fixed_finrank v

open OrthogonalDuality

/-- The inner cocode fixed space is dual to the actual pair perpendicular. -/
def innerOrthogonalDualEquiv (h : InnerRestrictionInput O) (h24 : AmbientFixedInput O) :
    InnerFixed ≃ₗ[ZMod 2] Module.Dual (ZMod 2) perpendicular :=
  fixedPerpendicularDualEquiv h h24.displacement h24.fixed_finrank

/-- The outer cocode fixed space has the same orthogonal dual description. -/
def outerOrthogonalDualEquiv (h : OuterRestrictionInput O) (h24 : AmbientFixedInput O) :
    OuterFixed ≃ₗ[ZMod 2] Module.Dual (ZMod 2) perpendicular :=
  fixedPerpendicularDualEquiv
    (f := MonoidHom.id m22PairStabilizer) (K := m22OuterHexadKernel O)
    h h24.displacement h24.fixed_finrank

theorem innerOrthogonalDualEquiv_equivariant (h : InnerRestrictionInput O)
    (h24 : AmbientFixedInput O) (g : m22InnerHexadStabilizer O) (v : InnerFixed) :
    innerOrthogonalDualEquiv h h24
      (innerQuotientRepresentation h h24 (QuotientGroup.mk g) v) =
      (perpendicularRepresentation m22ToPairStabilizer).dual g
        (innerOrthogonalDualEquiv h h24 v) :=
  fixedPerpendicularDualEquiv_equivariant h h24.displacement h24.fixed_finrank g v

theorem outerOrthogonalDualEquiv_equivariant (h : OuterRestrictionInput O)
    (h24 : AmbientFixedInput O) (g : m22OuterHexadStabilizer O) (v : OuterFixed) :
    outerOrthogonalDualEquiv h h24
      (outerQuotientRepresentation h h24 (QuotientGroup.mk g) v) =
      (perpendicularRepresentation (MonoidHom.id m22PairStabilizer)).dual g
        (outerOrthogonalDualEquiv h h24 v) :=
  fixedPerpendicularDualEquiv_equivariant h h24.displacement h24.fixed_finrank g v

/-- The orthogonal space has rank five and trivial quadratic radical, and the
marked pair is nonsingular. This form belongs to the dual module described above. -/
theorem orthogonal_geometry :
    Module.finrank (ZMod 2) perpendicular = 5 ∧
      perpendicularQuadratic.radical = ⊥ ∧ perpendicularQuadratic perpendicularPair = 1 :=
  ⟨finrank_perpendicular, perpendicularQuadratic_radical_eq_bot, perpendicularQuadratic_pair⟩

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.CocodeAction.SixPointModel
