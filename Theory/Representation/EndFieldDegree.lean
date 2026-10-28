module

public import Theory.Representation.EndFieldInvariants
public import Mathlib.Algebra.CharP.Algebra

/-!
# Faithfulness and dimensions over the Schur field

The endomorphism-field representation has exactly the original action maps,
so it preserves faithfulness. Its dimension and every subgroup-fixed
codimension multiply by the degree of the endomorphism field on restriction
of scalars. Consequently lower bounds for absolutely irreducible degrees
apply to irreducible representations over a smaller finite field.

This supplies scalar descent in the cross-characteristic degree argument of
Guralnick–Malle, Classification of 2F-modules I, §2 and Proposition 4.6.
Only the original actor is made linear over its Schur field; no scalar
linearity of additional normalizing operators is asserted.
-/

public section
open scoped MonoidAlgebra
namespace Representation
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  (ρ : Representation F G V)

/-- Scalar descent preserves the literal faithful action. -/
theorem endFieldRep_injective_iff :
    Function.Injective ρ.endFieldRep ↔ Function.Injective ρ := by
  constructor
  · intro h a b hab
    apply h
    ext v
    exact congrArg ρ.asModuleEquiv.symm (LinearMap.congr_fun hab (ρ.asModuleEquiv v))
  · intro h a b hab
    apply h
    ext v
    exact congrArg ρ.asModuleEquiv (LinearMap.congr_fun hab (ρ.asModuleEquiv.symm v))

variable [Finite F] [FiniteDimensional F V] [IsIrreducible ρ]

/-- The actual scalar tower relates the two representation degrees. -/
theorem finrank_eq_endField_mul :
    Module.finrank F V = Module.finrank F (Module.End F[G] ρ.asModule) *
      Module.finrank (Module.End F[G] ρ.asModule) ρ.asModule := by
  rw [Module.finrank_mul_finrank, ρ.asModuleEquiv.finrank_eq]

/-- Forgetting the larger finite scalar field cannot decrease degree. -/
theorem endField_finrank_le :
    Module.finrank (Module.End F[G] ρ.asModule) ρ.asModule ≤ Module.finrank F V := by
  let : FiniteDimensional F (Module.End F[G] ρ.asModule) := Module.Finite.of_finite
  have hp : 0 < Module.finrank F (Module.End F[G] ρ.asModule) := Module.finrank_pos
  rw [finrank_eq_endField_mul ρ]
  exact Nat.le_mul_of_pos_left _ hp

/-- Fixed codimension also multiplies by the degree of the Schur field. -/
theorem finrank_quotient_invariants_eq_endField_mul (A : Subgroup G) :
    Module.finrank F (V ⧸ invariants (ρ.comp A.subtype)) =
      Module.finrank F (Module.End F[G] ρ.asModule) *
        Module.finrank (Module.End F[G] ρ.asModule)
          (ρ.asModule ⧸ invariants (ρ.endFieldRep.comp A.subtype)) := by
  let E := Module.End F[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite F
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  have hF := (invariants (ρ.comp A.subtype)).finrank_quotient_add_finrank
  have hE := (invariants (ρ.endFieldRep.comp A.subtype)).finrank_quotient_add_finrank
  rw [finrank_eq_endField_mul ρ, finrank_invariants_eq_endField_mul ρ A] at hF
  have hm := congrArg (fun n : ℕ => Module.finrank F E * n) hE
  rw [Nat.mul_add] at hm
  exact Nat.add_right_cancel (hF.trans hm.symm)

end Representation

namespace Representation
universe u w

/-- A uniform degree bound for faithful absolutely irreducible actions over
finite fields of characteristic two descends to every irreducible binary action. -/
public theorem binary_finrank_ge_of_absolute_bound
    {G : Type u} [Group G] {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible) (d : ℕ)
    (hdegree : ∀ (K : Type w) [Field K] [Finite K] [CharP K 2]
      (U : Type w) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (τ : Representation K G U), Function.Injective τ →
        τ.IsAbsolutelyIrreducible → d ≤ Module.finrank K U) :
    d ≤ Module.finrank (ZMod 2) V := by
  let := hi
  let E := Module.End (ZMod 2)[G] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  exact (hdegree E ρ.asModule ρ.endFieldRep
    ((endFieldRep_injective_iff ρ).mpr hf)
    (endFieldRep_isAbsolutelyIrreducible ρ)).trans (endField_finrank_le ρ)

end Representation
