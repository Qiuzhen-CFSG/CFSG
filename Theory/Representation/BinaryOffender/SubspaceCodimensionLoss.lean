module

public import Theory.Representation.BinaryOffender.SectionLinear

/-!+# Loss of fixed codimension on an invariant subspace

Restricting an action to a subspace of codimension c loses at most c in
fixed codimension. The inclusion of its fixed space into the ambient fixed
space, followed by rank-nullity, proves this bound.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
K.4.4 and K.4.4's M₁₂ subsection, printed pp.459–460. The invariant
hyperplanes there lose at most one dimension.
-/

public section
namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Restriction loses at most the codimension of the invariant subspace. -/
theorem fixedCodim_le_subrepresentation_add_codim (W : Subrepresentation ρ)
    (A : Subgroup G) :
    fixedCodim ρ A ≤ fixedCodim W.toRepresentation A +
      Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) := by
  have he := (subrepresentationFixedEquiv ρ W A).finrank_eq
  have hle := Submodule.finrank_mono
    (show W.toSubmodule ⊓ fixedSpace ρ A ≤ fixedSpace ρ A from inf_le_right)
  have hv := fixedCodim_add_finrank ρ A
  have hw := fixedCodim_add_finrank W.toRepresentation A
  have hdim := W.toSubmodule.finrank_quotient_add_finrank
  omega

/-- A strict bound survives restriction if it has room for the lost dimensions. -/
theorem lt_fixedCodim_subrepresentation_of_add_codim_lt (W : Subrepresentation ρ)
    (A : Subgroup G) {n : ℕ}
    (h : n + Module.finrank (ZMod 2) (V ⧸ W.toSubmodule) < fixedCodim ρ A) :
    n < fixedCodim W.toRepresentation A := by
  have := fixedCodim_le_subrepresentation_add_codim ρ W A
  omega

end Representation.BinaryOffender
