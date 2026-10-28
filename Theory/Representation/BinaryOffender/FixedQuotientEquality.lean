module

public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Fixed spaces under a sharp equivariant quotient

When a surjective equivariant linear map preserves the codimension of a fixed
space, the original fixed space is the full inverse image of the quotient fixed
space. The induced map on fixed-space quotients is a surjection of equal finite
dimensions and hence injective. In particular every fixed quotient vector has a
fixed lift, without a splitting assumption.

This is the fixed-vector lifting step in Aschbacher–Smith B.2.20 and B.6.10,
printed pp.82 and 117, applied after the sharp natural-module offender bound.
-/

public section
namespace Representation.BinaryOffender
variable {H U V : Type*} [Group H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) V]
/-- Equality in the fixed-codimension quotient inequality forces equality of
fixed spaces with the full inverse image. -/
theorem fixedSpace_eq_comap_of_fixedCodim_eq (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H V)
    (f : U →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (A : Subgroup H)
    (hd : fixedCodim ρ A = fixedCodim σ A) :
    fixedSpace ρ A = (fixedSpace σ A).comap f := by
  have hfix : fixedSpace ρ A ≤ (fixedSpace σ A).comap f := by
    intro u hu a
    change σ a (f u) = f u
    rw [← he]
    exact congrArg f (hu a)
  let q := (fixedSpace ρ A).mapQ (fixedSpace σ A) f hfix
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w, rfl⟩ := (fixedSpace σ A).mkQ_surjective v
    obtain ⟨u, rfl⟩ := hf w
    exact ⟨(fixedSpace ρ A).mkQ u, rfl⟩
  have hi : Function.Injective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hq
  apply le_antisymm hfix
  intro u hu
  have hz : q ((fixedSpace ρ A).mkQ u) = q 0 := by
    change (fixedSpace σ A).mkQ (f u) = q 0
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hu
  exact (Submodule.Quotient.mk_eq_zero _).mp (hi hz)

end Representation.BinaryOffender
