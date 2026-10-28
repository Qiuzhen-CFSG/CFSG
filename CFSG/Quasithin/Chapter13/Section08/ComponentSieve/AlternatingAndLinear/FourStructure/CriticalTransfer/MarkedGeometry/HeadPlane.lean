module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry

/-!
# The marked two-plane in the chosen natural head

The generating seed injects into every proper quotient. Composing that
injection with the specified equivariant natural identification constructs
its actual image plane, proves its dimension is two, and places the marked
seed stabilizer in the plane stabilizer. The group identification and head
coordinates remain fixed throughout. Equality with the full parabolic and
the placement of its two-core in the radical are not asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.960–961 (PDF pp.977–978).
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- The actual image of the marked generating two-space in the chosen head
coordinates. The head and the group identification are never changed. -/
def headSeedMap (s : GeneratingSeed ρ) (W : Subrepresentation ρ)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace) :
    s.space.toSubmodule →ₗ[ZMod 2] ChiefFactors.NaturalSpace :=
  e.toLinearMap.comp (W.toSubmodule.mkQ.comp s.space.toSubmodule.subtype)

def headPlane (s : GeneratingSeed ρ) (W : Subrepresentation ρ)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace) :
    Submodule (ZMod 2) ChiefFactors.NaturalSpace := LinearMap.range (headSeedMap ρ s W e)

theorem headPlane_finrank (s : GeneratingSeed ρ) (W : Subrepresentation ρ)
    (hW : W ≠ ⊤) (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace) :
    Module.finrank (ZMod 2) (headPlane ρ s W e) = 2 := by
  have hi : Function.Injective (headSeedMap ρ s W e) :=
    e.injective.comp (s.quotient_injective ρ W hW)
  exact (LinearMap.finrank_range_of_inj hi).trans s.dim_two

theorem headPlane_stable (s : GeneratingSeed ρ) (W : Subrepresentation ρ)
    (eH : H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace)
    (he : ∀ g u, e (W.quotientRepresentation g u) = eH g (e u)) :
    s.parabolic.map eH.toMonoidHom ≤ BinaryLinear.parabolic (headPlane ρ s W e) := by
  have stable : ∀ g ∈ s.parabolic, ∀ v ∈ headPlane ρ s W e,
      eH g v ∈ headPlane ρ s W e := by
    intro g hg v hv
    obtain ⟨u, rfl⟩ := hv
    let w : s.space.toSubmodule := ⟨ρ g u, s.space.apply_mem_toSubmodule ⟨g, hg⟩ u.property⟩
    refine ⟨w, ?_⟩
    change e (W.toSubmodule.mkQ (ρ g u)) = eH g (e (W.toSubmodule.mkQ u))
    exact he g (W.toSubmodule.mkQ u)
  rintro _ ⟨g, hg, rfl⟩ v
  change eH g v ∈ headPlane ρ s W e ↔ v ∈ headPlane ρ s W e
  constructor
  · intro hv
    have hh := stable g⁻¹ (s.parabolic.inv_mem hg) _ hv
    simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using hh
  · exact stable g hg v

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
