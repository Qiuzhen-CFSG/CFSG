module

public import Theory.Representation.SU3.FiveSmallModules.Lifts
public import Theory.Representation.EndFieldDegree
public import Theory.Representation.BinaryOffender.Basic

/-!
# Binary descent for the small PSU₃(5) module calculation

The two predicates below specify the exhaustive absolute degree window
and the restriction to an actual order-seven element. They are independent
representation-theoretic obligations, not assertions of those calculations.

For an irreducible binary action, its actual Schur field makes the same
action absolutely irreducible. Absolute degree 20 or 21 and binary degree
at most 24 force the Schur-field degree to be one. The existing invariant
space equivalence then transports displacement 18 to the original binary
module. No absolute irreducibility or field of definition is assumed of
that original module.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section
open Subgroup Representation
open scoped MonoidAlgebra

namespace Representation.SU3.FiveSmallModules

universe u v

/-- The exhaustive small absolute degrees, with the coefficient field unrestricted. -/
def AbsoluteDegreeWindow (R : Type u) [Group R] : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K R U), Function.Injective τ →
    τ.IsAbsolutelyIrreducible → Module.finrank K U ≤ 24 →
      Module.finrank K U = 20 ∨ Module.finrank K U = 21

/-- The literal cyclic restriction on every small absolute module and projective
order-seven actor that itself has order seven. -/
def AbsoluteSevenRestriction (R : Type u) [Group R] : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K R U), Function.Injective τ →
    τ.IsAbsolutelyIrreducible →
    (Module.finrank K U = 20 ∨ Module.finrank K U = 21) →
    ∀ x : R, orderOf x = 7 → orderOf (QuotientGroup.mk' (center R) x) = 7 →
      Module.finrank K (U ⧸ invariants (τ.comp (zpowers x).subtype)) = 18

/-- Descent on the actual Schur-field representation preserves the binary degree
and the exact displacement of each order-seven actor. Both concrete calculations
remain explicit inputs. -/
theorem binary_degree_and_seven_displacement_of_absolute_inputs
    {R : Type u} [Group R] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) R V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 24)
    (hdegree : AbsoluteDegreeWindow.{u, v} R)
    (hseven : AbsoluteSevenRestriction.{u, v} R) :
    (Module.finrank (ZMod 2) V = 20 ∨ Module.finrank (ZMod 2) V = 21) ∧
      ∀ x : R, orderOf x = 7 → orderOf (QuotientGroup.mk' (center R) x) = 7 →
        BinaryOffender.fixedCodim ρ (zpowers x) = 18 := by
  let E := Module.End (ZMod 2)[R] ρ.asModule
  let : Finite ρ.asModule := Module.finite_of_finite (ZMod 2)
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  have hfE := (endFieldRep_injective_iff ρ).mpr hf
  have hiE := endFieldRep_isAbsolutelyIrreducible ρ
  have hD := hdegree E ρ.asModule ρ.endFieldRep hfE hiE ((endField_finrank_le ρ).trans hd)
  have hmul := finrank_eq_endField_mul ρ
  change Module.finrank (ZMod 2) V =
    Module.finrank (ZMod 2) E * Module.finrank E ρ.asModule at hmul
  have hpos : 0 < Module.finrank (ZMod 2) E := Module.finrank_pos
  have hE : Module.finrank (ZMod 2) E = 1 := by
    rcases hD with hD | hD
    · rw [hD] at hmul
      change Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) E * 20 at hmul
      omega
    · rw [hD] at hmul
      change Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) E * 21 at hmul
      omega
  have hdim : Module.finrank (ZMod 2) V = Module.finrank E ρ.asModule := by
    simpa only [hE, one_mul] using hmul
  refine ⟨by rw [hdim]; exact hD, ?_⟩
  intro x hx hxp
  have h18 := hseven E ρ.asModule ρ.endFieldRep hfE hiE hD x hx hxp
  change Module.finrank (ZMod 2) (V ⧸ invariants (ρ.comp (zpowers x).subtype)) = 18
  rw [finrank_quotient_invariants_eq_endField_mul ρ (zpowers x), hE, h18, one_mul]

end Representation.SU3.FiveSmallModules
