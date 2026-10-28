module

public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Faithful kernel quotients in the original actor universe

The quotient by the action kernel acts faithfully on the same vector space.
Its canonical equivalence with the action image transports best offenders and
identifies their literal subgroup maps. Keeping the quotient carrier in the
original group universe permits induction on module dimension without a
universe change in the actors.

Source applications: GLS2, Theorem 26.24, Step 1; Aschbacher--Smith B.5.1.
-/

@[expose] public noncomputable section
open Subgroup
namespace Representation.BinaryOffender.KernelQuotient
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

abbrev Actor := G ⧸ (actionHom ρ).ker
abbrev projection : G →* Actor ρ := QuotientGroup.mk' (actionHom ρ).ker

def equiv : Actor ρ ≃* actionImage ρ :=
  QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective

def action : Representation (ZMod 2) (Actor ρ) V :=
  (imageRepresentation ρ).comp (equiv ρ).toMonoidHom

theorem equiv_projection (g : G) : equiv ρ (projection ρ g) = actionHom ρ g := rfl

theorem action_projection (g : G) : action ρ (projection ρ g) = ρ g := rfl

theorem projection_surjective : Function.Surjective (projection ρ) :=
  QuotientGroup.mk'_surjective _

theorem faithful : Function.Injective (action ρ) :=
  (imageRepresentation_injective ρ).comp (equiv ρ).injective

/-- Every best offender on the action image has the same literal action on
its representative in the faithful kernel quotient, in the original universe. -/
theorem bestOffender_transport [FiniteDimensional (ZMod 2) V]
    {B : Subgroup (actionImage ρ)} (hB : IsBestOffender (imageRepresentation ρ) B) :
    IsBestOffender (action ρ) (B.map (equiv ρ).symm.toMonoidHom) := by
  apply hB.map_of_fixedCodim (imageRepresentation ρ) (action ρ)
    (equiv ρ).symm.toMonoidHom (equiv ρ).symm.injective
  intro A
  apply fixedCodim_map_equivariant (imageRepresentation ρ) (action ρ)
    (equiv ρ).symm.toMonoidHom (LinearEquiv.refl (ZMod 2) V)
  intro g v
  change imageRepresentation ρ g v = imageRepresentation ρ (equiv ρ ((equiv ρ).symm g)) v
  rw [(equiv ρ).apply_symm_apply]

theorem actionSubgroup_transport (A : Subgroup G) :
    (actionSubgroup ρ A).map (equiv ρ).symm.toMonoidHom = A.map (projection ρ) := by
  rw [actionSubgroup, Subgroup.map_map]
  congr 1
  ext g
  exact ((equiv ρ).symm_apply_apply (projection ρ g)).trans rfl

end Representation.BinaryOffender.KernelQuotient
