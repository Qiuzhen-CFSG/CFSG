module

public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphField
public import Theory.GroupAction.CentralKernelFixedResidual

/-!
# Canonical residual projections for the perfect four-cover

The covering map restricts to each of the three fixed-subgroup two-residuals.
Each restriction is surjective by the central-two-kernel displacement argument.
For graph-field this also proves the equality of embedded residual images
used in the projective pointwise-fixer calculation.

These results preserve the specified graph and field lifts. They do not
identify the residual groups or assert injectivity of their projections.
Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137 (1 March 2004).
-/

public section

namespace Matrix.PSL3Four
variable {E : Type*} [Group E] {c : FourCover E}

/-- The cover kernel is a two-group, directly from its Klein four structure. -/
theorem FourCover.ker_isTwoGroup (c : FourCover E) : IsPGroup 2 c.toMonoidHom.ker := by
  rw [c.ker_eq_center]
  let := c.center_isKleinFour
  exact IsPGroup.of_card (n := 2) (by simp)

/-- The graph fixed-residual projection, on the specified matrix quotient. -/
@[expose] noncomputable def CoverActions.graphResidualProjection (a : CoverActions E c) :
    pResidual 2 a.graph.fixedSubgroup →*
      pResidual 2 (PSL3.OuterSolvable.graph F).fixedSubgroup :=
  MulAut.fixedResidualMap 2 _ _ c.toMonoidHom a.graph_compatible

/-- The field fixed-residual projection. -/
@[expose] noncomputable def CoverActions.fieldResidualProjection (a : CoverActions E c) :
    pResidual 2 a.field.fixedSubgroup →* pResidual 2 pslFrobenius.fixedSubgroup :=
  MulAut.fixedResidualMap 2 _ _ c.toMonoidHom a.field_compatible

/-- The graph-field fixed-residual projection. -/
@[expose] noncomputable def CoverActions.graphFieldResidualProjection (a : CoverActions E c) :
    pResidual 2 a.graphField.fixedSubgroup →*
      pResidual 2 (PSL3.OuterSolvable.graph F * pslFrobenius).fixedSubgroup :=
  MulAut.fixedResidualMap 2 _ _ c.toMonoidHom a.graphField_compatible

variable [Finite E]

/-- Every element of the projective graph residual has a fixed residual lift. -/
theorem CoverActions.graphResidualProjection_surjective (a : CoverActions E c) :
    Function.Surjective a.graphResidualProjection :=
  MulAut.fixedResidualMap_surjective 2 _ _ c.toMonoidHom c.surjective
    c.ker_le_center c.ker_isTwoGroup a.graph_compatible

/-- Every element of the projective field residual has a fixed residual lift. -/
theorem CoverActions.fieldResidualProjection_surjective (a : CoverActions E c) :
    Function.Surjective a.fieldResidualProjection :=
  MulAut.fixedResidualMap_surjective 2 _ _ c.toMonoidHom c.surjective
    c.ker_le_center c.ker_isTwoGroup a.field_compatible

/-- Every element of the projective graph-field residual has a fixed residual lift. -/
theorem CoverActions.graphFieldResidualProjection_surjective (a : CoverActions E c) :
    Function.Surjective a.graphFieldResidualProjection :=
  MulAut.fixedResidualMap_surjective 2 _ _ c.toMonoidHom c.surjective
    c.ker_le_center c.ker_isTwoGroup a.graphField_compatible

/-- The embedded graph-field residual projects onto the actual projective residual. -/
theorem CoverActions.graphFieldResidual_map (a : CoverActions E c) :
    a.graphFieldResidual.map c.toMonoidHom = projectiveGraphFieldResidual :=
  MulAut.map_embedded_fixedResidual_of_central_pgroup_ker 2 _ _ c.toMonoidHom
    c.surjective c.ker_le_center c.ker_isTwoGroup a.graphField_compatible

end Matrix.PSL3Four
