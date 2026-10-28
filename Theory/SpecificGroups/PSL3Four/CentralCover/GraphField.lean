module

public import Theory.SpecificGroups.PSL3Four.CentralCover
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.PResidual.Defs

/-!
# The actual graph-field residuals on the cover and its quotient

These subgroups are the embedded two-residuals of the fixed subgroups of
the specified graph-field automorphisms. The cover calculation must identify
the first with E₉ and prove that its projection is the second. The separate
projective calculation must bound the pointwise fixer of the second.

Source: Aschbacher--Smith 15.3.38, printed p.1137 (1 March 2004 manuscript).
No group-family label or asserted centralizer order enters these definitions.
-/

public section

namespace Matrix.PSL3Four

/-- The two-residual of the fixed subgroup of inverse transpose times Frobenius,
embedded in the actual projective matrix group. -/
@[expose] noncomputable def projectiveGraphFieldResidual : Subgroup PSL :=
  (pResidual 2 (PSL3.OuterSolvable.graph F * pslFrobenius).fixedSubgroup).map
    (PSL3.OuterSolvable.graph F * pslFrobenius).fixedSubgroup.subtype

/-- The corresponding embedded subgroup of the perfect four-cover. -/
@[expose] def CoverActions.graphFieldResidual {E : Type*} [Group E]
    {c : FourCover E} (a : CoverActions E c) : Subgroup E :=
  (pResidual 2 a.graphField.fixedSubgroup).map a.graphField.fixedSubgroup.subtype

end Matrix.PSL3Four
