module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.Induction
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients

/-!
# Excluding central F₄ degree twelve for the triple Mathieu cover

A marked faithful irreducible action of F₄ degree twelve restricts to an
irreducible binary action of degree twenty-four. The point-filtration and
Frobenius-reciprocity argument reduces its exclusion to the absence of
simple degree-twenty-four quotients in the two concrete induced point modules.
Their checked filtrations have simple binary factors of dimensions 12, 30
and 90, so the induced-quotient exclusions discharge both branches. This proves
the central-field exclusion without assuming absolute irreducibility, a
specified endomorphism field, or splitting of the point restriction.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16 and Theorem 6.6/Table 6.7; Aschbacher–Smith H.12.1, pp.393–394.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
open Representation Uniqueness.PointRestriction ExclusionsTwelve

universe u

/-- The two explicit induced-module calculations imply the required central-field exclusion. -/
theorem centralFieldDegreeExclusion_twelve_of_induced
    (hc : ∀ a, ExclusionsTwelve.InducedQuotientExclusion.{u} a) :
    CentralFieldDegreeExclusion.{u} 12 := by
  intro W _ _ _ τ hf hi hs hd
  let := hi
  let : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) F)
  let : IsScalarTower (ZMod 2) F W := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : FiniteDimensional (ZMod 2) W := Module.Finite.trans F W
  let ρ := restrictScalars (k := ZMod 2) τ
  let : ρ.IsIrreducible := ExclusionsTwelve.restrictScalars_isIrreducible τ hs
  have hf' : Function.Injective ρ := ExclusionsTwelve.restrictScalars_faithful τ hf
  have he := Module.finrank_mul_finrank (ZMod 2) F W
  rw [QuadraticAlgebra.finrank_eq_two, hd] at he
  exact binary_exclusion_of_induced ρ hc hf' (by omega)

/-- A faithful irreducible F₄ action with the marked central scalar cannot have
dimension twelve. Both concrete induced-module exclusions are discharged. -/
theorem centralFieldDegreeExclusion_twelve : CentralFieldDegreeExclusion.{u} 12 :=
  centralFieldDegreeExclusion_twelve_of_induced inducedQuotientExclusion

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
