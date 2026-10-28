module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.Coordinates
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Scalars
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Action
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FieldFlag
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FactorAlgebras

/-!
# The dual induced point-module filtration

The first 45 and 51 columns of the certified basis give an invariant flag in
the actual 66-dimensional induced coordinate action over F₄. Its literal
successive quotients have dimensions 45, 6 and 15. The checked rank-one
certificates show that their generator matrices span the full matrix algebras,
so all three quotients are simple.

The square of the central scalar acts by omega on the dual induced action.
Consequently restriction to F₂ preserves simplicity and doubles the quotient
dimensions to 90, 12 and 30. The unconditional binary filtration is the witness
required by the parent's induced-quotient exclusion consumer.

Source context: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16, and Theorem 6.6/Table 6.7. This particular induced
filtration is an independent calculation supporting the source degree gap.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates
open Representation

/-- Scalar descent for a proved filtration of the actual dual induced action. -/
theorem dual_factorDegreeFiltration_of_field
    (h : FactorDegreeFiltration ({6, 15, 45} : Set ℕ) (fieldRepresentation .dual)) :
    FactorDegreeFiltration ({12, 30, 90} : Set ℕ) (representation .dual) := by
  rw [← fieldRepresentation_restrictScalars]
  apply DualFiltration.restrict_filtration (scalar ^ 2) ?_ h
    DualFiltration.fieldRepresentation_dual_scalar_sq
  intro d hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd ⊢
  rcases hd with rfl | rfl | rfl <;> simp

/-- The certified column flag has simple factors of dimensions 45, 6 and 15 over F₄. -/
theorem DualFiltration.field_factorDegreeFiltration :
    FactorDegreeFiltration ({6, 15, 45} : Set ℕ) (fieldRepresentation .dual) :=
  DualFiltration.field_factorDegreeFiltration_of_matrix_algebras
    DualFiltration.factorMatrix_algebra_eq_top

/-- The actual dual induced point module has simple binary factors of dimensions
90, 12 and 30, with no splitting or composition-factor hypothesis. -/
theorem dual_factorDegreeFiltration :
    FactorDegreeFiltration ({12, 30, 90} : Set ℕ) (representation .dual) :=
  dual_factorDegreeFiltration_of_field DualFiltration.field_factorDegreeFiltration

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates
