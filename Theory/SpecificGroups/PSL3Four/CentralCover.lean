module

public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The perfect four-cover and compatible graph and field lifts

The covering map here lands in the actual quotient `SL₃(4)/Z(SL₃(4))`.
Its kernel is exactly the center and is a Klein four-group. The action data
specify lifts of inverse transpose and entrywise Frobenius through that same
map. Faithful descent proves that the lifts square to one and commute;
these conclusions are not fields of the input record.

This interface supports the intrinsic model calculations in Aschbacher--Smith
15.3.38, printed pp.1136--1137 (1 March 2004 manuscript). It does not assert
involution fusion, fixed-subgroup models, or an overgroup structure. In
particular, the choice of ambient lifts and the diagonal action in the source
must still be supplied when studying the larger centralizer in `I`.
-/

public section

namespace Matrix.PSL3Four
variable (E : Type*) [Group E]

/-- A perfect central cover with the actual PSL₃(4) quotient and center E₄. -/
structure FourCover extends PerfectCentralCovering.Cover E PSL where
  ker_eq_center : toMonoidHom.ker = Subgroup.center E
  center_isKleinFour : IsKleinFour (Subgroup.center E)

/-- Graph and field automorphisms lifted compatibly through the covering map. -/
structure CoverActions (c : FourCover E) where
  graph : MulAut E
  field : MulAut E
  graph_compatible : ∀ x : E, c.toMonoidHom (graph x) =
    PSL3.OuterSolvable.graph F (c.toMonoidHom x)
  field_compatible : ∀ x : E, c.toMonoidHom (field x) =
    pslFrobenius (c.toMonoidHom x)

variable {E}

theorem CoverActions.graph_descends {c : FourCover E} (a : CoverActions E c) :
    c.toCover.autMap c.ker_eq_center a.graph = PSL3.OuterSolvable.graph F := by
  ext x
  obtain ⟨y, rfl⟩ := c.surjective x
  rw [c.toCover.autMap_apply, a.graph_compatible]

theorem CoverActions.field_descends {c : FourCover E} (a : CoverActions E c) :
    c.toCover.autMap c.ker_eq_center a.field = pslFrobenius := by
  ext x
  obtain ⟨y, rfl⟩ := c.surjective x
  rw [c.toCover.autMap_apply, a.field_compatible]

theorem CoverActions.graph_sq {c : FourCover E} (a : CoverActions E c) :
    a.graph ^ 2 = 1 := by
  apply c.toCover.autMap_injective c.ker_eq_center
  rw [map_pow, map_one, a.graph_descends, PSL3.OuterSolvable.graph_sq]

theorem CoverActions.field_sq {c : FourCover E} (a : CoverActions E c) :
    a.field ^ 2 = 1 := by
  apply c.toCover.autMap_injective c.ker_eq_center
  rw [map_pow, map_one, a.field_descends, pslFrobenius_sq]

/-- The graph-field product on the cover. -/
@[expose] def CoverActions.graphField {c : FourCover E} (a : CoverActions E c) : MulAut E :=
  a.graph * a.field

theorem CoverActions.graphField_compatible {c : FourCover E} (a : CoverActions E c)
    (x : E) : c.toMonoidHom (a.graphField x) =
      (PSL3.OuterSolvable.graph F * pslFrobenius) (c.toMonoidHom x) := by
  change c.toMonoidHom (a.graph (a.field x)) = _
  rw [a.graph_compatible, a.field_compatible]
  rfl

theorem graph_commutes_frobenius :
    Commute (PSL3.OuterSolvable.graph F) pslFrobenius := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) x
  change PSL3.OuterSolvable.graph F (pslFrobenius (y : PSL)) =
    pslFrobenius (PSL3.OuterSolvable.graph F (y : PSL))
  rw [pslFrobenius_mk, PSL3.OuterSolvable.graph_mk,
    PSL3.OuterSolvable.graph_mk, pslFrobenius_mk]
  congr 1
  rw [map_inv]
  congr 1

theorem CoverActions.graph_commutes_field {c : FourCover E} (a : CoverActions E c) :
    Commute a.graph a.field := by
  apply c.toCover.autMap_injective c.ker_eq_center
  rw [map_mul, map_mul, a.graph_descends, a.field_descends]
  exact graph_commutes_frobenius

theorem CoverActions.graphField_sq {c : FourCover E} (a : CoverActions E c) :
    a.graphField ^ 2 = 1 := by
  rw [graphField, a.graph_commutes_field.mul_pow, a.graph_sq, a.field_sq, mul_one]

end Matrix.PSL3Four
