module

public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.Representation.EndFieldDegree
public import Theory.Representation.InvariantsBaseChange

/-!
# Fixed codimension through the Schur field

For finite groups, the fixed-space equations commute with scalar extension,
also in defining characteristic. Passing from a binary irreducible through
its actual Schur field to its algebraic closure therefore multiplies every
subgroup-fixed codimension by precisely the Schur-field degree.

This is the fixed-space version of the dimension descent in GLS3, Remark
2.8.8, used for the involution bounds in Guralnick--Malle II, Lemma 8.8.
It does not assert any model-specific fixed-space bound.
-/

public section
open scoped TensorProduct
open Representation
namespace ReeF4.FixedSpaceEstimate

/-- Scalar extension preserves the codimension of the literal subgroup invariants. -/
theorem fixedCodim_extendScalars
    {F E G V : Type*} [Field F] [Field E] [Algebra F E]
    [Group G] [Finite G] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (A : Subgroup G) :
    Module.finrank E ((E ⊗[F] V) ⧸ invariants ((extendScalars E ρ).comp A.subtype)) =
      Module.finrank F (V ⧸ invariants (ρ.comp A.subtype)) := by
  have he : (extendScalars E ρ).comp A.subtype = extendScalars E (ρ.comp A.subtype) := rfl
  rw [he, Submodule.finrank_quotient, Submodule.finrank_quotient,
    finrank_invariants_extendScalars_eq_of_finite, Module.finrank_baseChange]

open Representation.FrobeniusTensor

/-- Exact scalar descent for the absolute action of a binary irreducible. -/
theorem binary_fixedCodim_eq_schur_mul
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (A : Subgroup G) :
    Module.finrank (ZMod 2) (V ⧸ invariants (ρ.comp A.subtype)) =
      Module.finrank (ZMod 2) (SchurField ρ) *
        Module.finrank (Closure ρ)
          (AbsoluteSpace ρ ⧸ invariants ((absoluteRep ρ).comp A.subtype)) := by
  rw [finrank_quotient_invariants_eq_endField_mul]
  exact congrArg (Module.finrank (ZMod 2) (SchurField ρ) * ·)
    (fixedCodim_extendScalars (E := Closure ρ) ρ.endFieldRep A).symm

/-- An estimate for every absolute character period descends using the actual
Schur degree. Tensor classification supplies the full period; the tensor-rank
argument supplies the estimate. Neither is asserted here. -/
theorem binary_fixedCodim_ge_of_period_estimate
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (A : Subgroup G) {n b : ℕ}
    (hperiod : ∀ g, (absoluteRep ρ).character g ^ (2 ^ n) = (absoluteRep ρ).character g)
    (hestimate : ∀ s : ℕ, 0 < s → s ∣ n →
      (∀ g, (absoluteRep ρ).character g ^ (2 ^ s) = (absoluteRep ρ).character g) →
      b * n ≤ s * Module.finrank (Closure ρ)
        (AbsoluteSpace ρ ⧸ invariants ((absoluteRep ρ).comp A.subtype))) :
    b * n ≤ Module.finrank (ZMod 2) (V ⧸ invariants (ρ.comp A.subtype)) := by
  rw [binary_fixedCodim_eq_schur_mul]
  exact hestimate _ (schurField_finrank_pos ρ) ((character_pow_iff ρ n).mp hperiod)
    ((character_pow_iff ρ _).mpr (dvd_refl _))

end ReeF4.FixedSpaceEstimate
