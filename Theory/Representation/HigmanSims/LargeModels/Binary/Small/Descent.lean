module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Sections
public import Theory.Representation.HigmanSims.Twenty.Marked
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Descent.Exterior
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Descent.Rows

/-!
# The marked small binary Higman–Sims actions

A marked degree-twenty action and a certified exterior-square row section
construct an action on the dual of the actual row quotient. The exterior
basis is indexed in the published 190-coordinate order. Row multiplication
uses the inverse group element, and standard duality removes that inverse;
evaluation at the lifted rows therefore gives the raw target matrices.

The two applications have degrees 56 and 132, with kernel dimensions 1 and
57 respectively. No simplicity, density, or presentation assumption is used.
The numerical certificates and degree-twenty comparison remain explicit inputs.

Source: ATLAS HSG1-f2r20B0, HSG1-f2r56B0 and HSG1-f2r132B0;
see `Binary/source/README.md` for the inverted permutation convention and
preserved attribution. Original proof code follows the repository license.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Small

/-- The certified row quotient gives a marked action of the literal HS carrier. -/
theorem nonempty_markedAction_of_section {i : Fin 4} {r : ℕ}
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison)
    (S : SectionCertificate i r) : Nonempty (MarkedAction i) := by
  obtain ⟨C⟩ := h20
  exact ⟨Descent.markedAction (Descent.ambientHom C)
    (Descent.ambientHom_a C) (Descent.ambientHom_b C) S⟩

/-- The literal degree-56 consumer, with its one-dimensional kernel. -/
theorem nonempty_markedAction_zero
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison)
    (S56 : SectionCertificate 0 1) : Nonempty (MarkedAction 0) :=
  nonempty_markedAction_of_section h20 S56

/-- The literal degree-132 consumer, with its 57-dimensional kernel. -/
theorem nonempty_markedAction_one
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison)
    (S132 : SectionCertificate 1 57) : Nonempty (MarkedAction 1) :=
  nonempty_markedAction_of_section h20 S132

end Representation.HigmanSims.LargeModels.Binary.Small
