module

public import Theory.Representation.BinaryOffender.SubspaceCodimensionLoss

/-!
# Fixed vectors in a saturated invariant subspace

Equality in the bound for the loss of fixed codimension on an invariant
subspace forces every ambient fixed vector into that subspace. The proof
compares the dimension of the intersection with the full fixed space.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, 13.8.23(1), printed p.958, combined manuscript, 1 March 2004.
-/

public section
open Subgroup Representation

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
theorem fixedSpace_le_of_saturated_codimension (ρ : Representation (ZMod 2) G V)
    (W : Subrepresentation ρ) (A : Subgroup G)
    (he : fixedCodim ρ A = fixedCodim W.toRepresentation A +
      Module.finrank (ZMod 2) (V ⧸ W.toSubmodule)) :
    fixedSpace ρ A ≤ W.toSubmodule := by
  have hi := (subrepresentationFixedEquiv ρ W A).finrank_eq
  have hv := fixedCodim_add_finrank ρ A
  have hw := fixedCodim_add_finrank W.toRepresentation A
  have hd := W.toSubmodule.finrank_quotient_add_finrank
  have hEq : W.toSubmodule ⊓ fixedSpace ρ A = fixedSpace ρ A :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  exact hEq ▸ inf_le_left
end Representation.BinaryOffender
