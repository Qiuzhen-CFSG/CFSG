module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.Divisibility
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.FieldReduction
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.PointConstituents
public import Theory.Representation.Mathieu.M22James.MinimumDegree
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel

/-!
# Reductions for the binary degree-twenty-four window of 3.M₂₂

Every faithful irreducible binary action of the actual triple cover in this
window has degree 12, 18, or 24. On its forced central F₄ structure the same
faithful action is irreducible and has degree 6, 9, or 12. This is not a
prescribed Schur field and does not assert absolute irreducibility.

The literal point restriction is transported through the checked SL₃(4)
equivalence, with its central element retained. If that restriction is simple,
its binary degree must be eighteen. Every simple submodule of the restriction
has degree six or eighteen; the possible numerical degree sixteen is excluded
using the actual quotient and the small central-character divisibility theorem.

The exclusion of full-group irreducibles of F₄ degree nine and twelve remains
required. None of these reductions asserts the degree gap itself.
Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16 and Theorem 6.6/Table 6.7; Aschbacher–Smith H.12.1, pp.393–394.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
open Representation
open Uniqueness Uniqueness.PointRestriction Uniqueness.PointRestriction.PointModel
open Representation.SL3FourLocalCatalogue

universe u

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) M22TripleCover V) [ρ.IsIrreducible]
  (hf : Function.Injective ρ)

include hf in
/-- Only the two larger multiples of six remain above the James minimum. -/
theorem binary_finrank_cases (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V = 12 ∨ Module.finrank (ZMod 2) V = 18 ∨
      Module.finrank (ZMod 2) V = 24 := by
  have hlo := faithful_irreducible_finrank_ge_twelve ρ hf
  have hdiv := six_dvd_finrank ρ hf
  omega

/-- The remaining dimensions over the field forced by the central scalar. -/
theorem field_finrank_cases (hd : Module.finrank (ZMod 2) V ≤ 24) :
    letI := Uniqueness.PointRestriction.fieldModule ρ hf
    Module.finrank Uniqueness.PointRestriction.F V = 6 ∨
      Module.finrank Uniqueness.PointRestriction.F V = 9 ∨
      Module.finrank Uniqueness.PointRestriction.F V = 12 := by
  let := Uniqueness.PointRestriction.fieldModule ρ hf
  have ht := twice_field_finrank ρ hf
  have hc := binary_finrank_cases ρ hf hd
  omega

/-- The original point action, transported through the actual subgroup equivalence. -/
def pointAction : Representation (ZMod 2) Representation.SL3FourLocalCatalogue.SL V :=
  (ρ.comp pointStabilizer.subtype).comp pointStabilizerEquiv.symm.toMonoidHom

omit [FiniteDimensional (ZMod 2) V] in
include hf in
/-- The transported central element is the original cover's central scalar. -/
theorem pointAction_centralQuadratic : CentralQuadratic (pointAction ρ) := by
  have hs : (pointStabilizerEquiv.symm SL3FourNaturalDual.centralScalar : pointStabilizer) =
      pointScalar := by
    apply pointStabilizerEquiv.injective
    rw [pointStabilizerEquiv.apply_symm_apply]
    exact pointStabilizerEquiv_pointScalar.symm
  change ρ ((pointStabilizerEquiv.symm SL3FourNaturalDual.centralScalar : pointStabilizer) :
      M22TripleCover) ^ 2 +
    ρ ((pointStabilizerEquiv.symm SL3FourNaturalDual.centralScalar : pointStabilizer) :
      M22TripleCover) + 1 = 0
  rw [hs]
  exact scalar_quadratic ρ hf

include hf in
/-- A simple point restriction in this window has degree eighteen and Schur degree two. -/
theorem point_irreducible_finrank [Representation.IsIrreducible (pointAction ρ)]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V = 18 ∧ schurDegree 2 (pointAction ρ) = 2 := by
  obtain ⟨hs, hc⟩ := PointConstituents.schurDegree_eq_two_and_finrank_cases
    (pointAction ρ) (pointAction_centralQuadratic ρ hf) hd
  have hdim := binary_finrank_cases ρ hf hd
  exact ⟨by omega, hs⟩

include hf in
/-- Every actual simple point submodule has degree six or eighteen. The quotient
 argument excludes the spurious numerical sixteen-dimensional possibility. -/
theorem point_simple_submodule_finrank
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (N : Subrepresentation (pointAction ρ)) [Representation.IsIrreducible N.toRepresentation] :
    Module.finrank (ZMod 2) N.toSubmodule = 6 ∨
      Module.finrank (ZMod 2) N.toSubmodule = 18 := by
  have hq := pointAction_centralQuadratic ρ hf
  obtain ⟨_, hn⟩ := PointConstituents.schurDegree_eq_two_and_finrank_cases
    N.toRepresentation (centralQuadratic_subrepresentation _ hq N)
    ((Submodule.finrank_le N.toSubmodule).trans hd)
  have hsum := Submodule.finrank_quotient_add_finrank N.toSubmodule
  have hdiv := six_dvd_finrank ρ hf
  rcases hn with hn | hn | hn
  · exact Or.inl hn
  · have hqdiv := PointConstituents.six_dvd_finrank_of_le_twelve N.quotientRepresentation
      (centralQuadratic_quotient _ hq N) (by omega)
    omega
  · exact Or.inr hn

include hf in
/-- Conditional assembly of the degree window. Its two premises are genuine
 remaining representation-theoretic exclusions, not consequences of uniqueness
 at degree twelve. The canonical central field discharges all scalar premises. -/
theorem finrank_eq_twelve_of_field_exclusions
    (h9 : CentralFieldDegreeExclusion.{u} 9) (h12 : CentralFieldDegreeExclusion.{u} 12)
    (hd : Module.finrank (ZMod 2) V ≤ 24) : Module.finrank (ZMod 2) V = 12 := by
  let := Uniqueness.PointRestriction.fieldModule ρ hf
  let := field_finiteDimensional ρ hf
  let τ := Uniqueness.PointRestriction.fieldRepresentation ρ hf
  have hi : τ.IsIrreducible := fieldRepresentation_isIrreducible ρ hf
  have hf' : Function.Injective τ := Uniqueness.PointRestriction.fieldRepresentation_faithful ρ hf
  have hs : ∀ v, τ scalar v = (QuadraticAlgebra.omega : Uniqueness.PointRestriction.F) • v :=
    Uniqueness.PointRestriction.field_scalar ρ hf
  have ht := twice_field_finrank ρ hf
  rcases field_finrank_cases ρ hf hd with he | he | he
  · omega
  · exact (h9 V τ hf' hi hs he).elim
  · exact (h12 V τ hf' hi hs he).elim

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour
