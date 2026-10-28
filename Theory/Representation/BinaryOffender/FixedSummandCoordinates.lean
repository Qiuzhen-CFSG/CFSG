module
public import Theory.Representation.BinaryOffender.FixedSummandTransport
public import Mathlib.LinearAlgebra.Projection
/-!
# Coordinates from a fixed direct summand

The addition equivalence for complementary submodules gives coordinates on a
representation as its invariant complement times its fixed space. In these
coordinates the actor acts only on the first factor. This preserves the literal
subrepresentation and is used for the seed projection in Aschbacher--Smith
15.1.28, printed p.1103.
-/

@[expose] public section
open Representation
namespace Subrepresentation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}
noncomputable def fixedSummandCoordinates (S : Subrepresentation ρ)
    (hc : IsCompl S.toSubmodule ρ.invariants) :
    V ≃ₗ[ZMod 2] S.toSubmodule × ρ.invariants :=
  (S.toSubmodule.prodEquivOfIsCompl ρ.invariants hc).symm

theorem fixedSummandCoordinates_intertwines (S : Subrepresentation ρ)
    (hc : IsCompl S.toSubmodule ρ.invariants) (g : G) (v : V) :
    S.fixedSummandCoordinates hc (ρ g v) =
      (S.toRepresentation g (S.fixedSummandCoordinates hc v).1,
        (S.fixedSummandCoordinates hc v).2) := by
  let e := S.toSubmodule.prodEquivOfIsCompl ρ.invariants hc
  change e.symm (ρ g v) = (S.toRepresentation g (e.symm v).1, (e.symm v).2)
  apply e.injective
  rw [e.apply_symm_apply]
  change ρ g v = ρ g ((e.symm v).1 : V) + ((e.symm v).2 : V)
  have hv : ((e.symm v).1 : V) + ((e.symm v).2 : V) = v := e.apply_symm_apply v
  conv_lhs => rw [← hv, map_add]
  rw [(e.symm v).2.property g]
end Subrepresentation
