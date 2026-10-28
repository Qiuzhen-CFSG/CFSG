module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Projection
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveField
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraph
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels
public import Theory.GroupTheory.CentralPPerfectCoprime
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# Reductions for the three four-cover fixed-residual models

The canonical projections and their surjectivity are proved in `Projection`.
For graph and field, injectivity identifies the cover residual with its
projective residual. For graph-field, an actual elementary nine-group model
of the projective residual already forces injectivity: the cover residual
is two-perfect and its central two-kernel vanishes by the coprime abelian
image argument. Thus no separate splitting hypothesis is used in that case.

These are conditional reductions for Aschbacher--Smith 15.3.38, printed
p.1137 (1 March 2004 manuscript). `ProjectiveField` proves the projective
field model. The graph and graph-field matrix calculations and the
graph/field kernel calculations remain to be supplied. The unconditional
embedded graph-field projection equality is re-exported here.
-/

public section

namespace Matrix.PSL3Four
variable {E : Type*} [Group E] [Finite E] {c : FourCover E}

/-- A projective elementary-nine model makes the graph-field projection injective. -/
theorem CoverActions.graphFieldResidualProjection_injective_of_projective_model (a : CoverActions E c)
    (e : pResidual 2 (PSL3.OuterSolvable.graph F * pslFrobenius).fixedSubgroup ≃*
      Multiplicative (Fin 2 → ZMod 3)) :
    Function.Injective a.graphFieldResidualProjection := by
  apply MonoidHom.injective_of_isPPerfect_of_coprime_abelian_image
    (Subgroup.isPPerfect_pResidual 2) a.graphFieldResidualProjection
    (MulAut.fixedResidualMap_ker_le_center 2 _ _ c.toMonoidHom
      a.graphField_compatible c.ker_le_center)
    (MulAut.fixedResidualMap_ker_isPGroup 2 _ _ c.toMonoidHom
      a.graphField_compatible c.ker_isTwoGroup)
  · intro x y
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  · exact (by decide : Nat.Coprime 2 3)
  · intro x
    apply e.injective
    rw [map_pow, map_one]
    change (3 : ℕ) • (e (a.graphFieldResidualProjection x)).toAdd = 0
    exact ZModModule.char_nsmul_eq_zero 3 _

/-- Lift a genuine projective graph-field residual model through the four-cover. -/
noncomputable def CoverActions.graphFieldResidualEquivOfProjectiveModel
    (a : CoverActions E c)
    (e : pResidual 2 (PSL3.OuterSolvable.graph F * pslFrobenius).fixedSubgroup ≃*
      Multiplicative (Fin 2 → ZMod 3)) :
    pResidual 2 a.graphField.fixedSubgroup ≃* Multiplicative (Fin 2 → ZMod 3) :=
  (MulEquiv.ofBijective a.graphFieldResidualProjection
    ⟨a.graphFieldResidualProjection_injective_of_projective_model e,
      a.graphFieldResidualProjection_surjective⟩).trans e

/-- The graph residual projection is an equivalence once its kernel is trivial. -/
noncomputable def CoverActions.graphResidualEquivOfInjective (a : CoverActions E c)
    (hinj : Function.Injective a.graphResidualProjection) :
    pResidual 2 a.graph.fixedSubgroup ≃*
      pResidual 2 (PSL3.OuterSolvable.graph F).fixedSubgroup :=
  MulEquiv.ofBijective a.graphResidualProjection ⟨hinj, a.graphResidualProjection_surjective⟩

/-- The field residual projection is an equivalence once its kernel is trivial. -/
noncomputable def CoverActions.fieldResidualEquivOfInjective (a : CoverActions E c)
    (hinj : Function.Injective a.fieldResidualProjection) :
    pResidual 2 a.field.fixedSubgroup ≃* pResidual 2 pslFrobenius.fixedSubgroup :=
  MulEquiv.ofBijective a.fieldResidualProjection ⟨hinj, a.fieldResidualProjection_surjective⟩

/-- The binary matrix model lifts once the field residual projection has trivial kernel. -/
noncomputable def CoverActions.fieldResidualEquivPSL3TwoOfInjective (a : CoverActions E c)
    (hinj : Function.Injective a.fieldResidualProjection) :
    pResidual 2 a.field.fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (a.fieldResidualEquivOfInjective hinj).trans projectiveFieldResidualEquiv

/-! The preceding conditional interfaces become unconditional for the specified
four-cover.  The graph and field cases use the exceptional-cover kernel
restriction theorem, while graph-field uses the coprime elementary-nine
argument. -/

/-- The graph fixed-subgroup two-residual of a compatible four-cover action is
PSL₂(4), on the concrete projective matrix carrier. -/
noncomputable def CoverActions.graphResidualEquivPSL2Four (a : CoverActions E c) :
    pResidual 2 a.graph.fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F :=
  (a.graphResidualEquivOfInjective
    (a.graphResidualProjection_injective_of_projective_model projectiveGraphResidualEquiv)).trans
      projectiveGraphResidualEquiv

/-- The field fixed-subgroup two-residual of a compatible four-cover action is
PSL₃(2), on the concrete projective matrix carrier. -/
noncomputable def CoverActions.fieldResidualEquivPSL3Two (a : CoverActions E c) :
    pResidual 2 a.field.fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  a.fieldResidualEquivPSL3TwoOfInjective a.fieldResidualProjection_injective

/-- The graph-field fixed-subgroup two-residual of a compatible four-cover
action is the elementary abelian group of order nine. -/
noncomputable def CoverActions.graphFieldResidualEquivElementaryNine
    (a : CoverActions E c) :
    pResidual 2 a.graphField.fixedSubgroup ≃*
      Multiplicative (Fin 2 → ZMod 3) :=
  a.graphFieldResidualEquivOfProjectiveModel projectiveGraphFieldResidualEquiv

end Matrix.PSL3Four
