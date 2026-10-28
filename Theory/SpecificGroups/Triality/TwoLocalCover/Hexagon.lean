module

public import Theory.SpecificGroups.Triality.TwoLocalCover.Geometry
public import Theory.AlgebraicGroup.BNPair.HexagonalGeometry.ApartmentCycle
public import Theory.AlgebraicGroup.BNPair.HexagonalGeometry.Girth
public import Theory.AlgebraicGroup.BNPair.HexagonalGeometry.CycleConjugacy

/-!+# The genuine triality parabolic hexagon

The two full root parabolics of the pinned D4 graph-field elementary central
quotient give an incidence graph of diameter at most six and girth twelve.
Its standard normalizer apartment is a simple twelve-cycle, and every simple
twelve-cycle is a translate by an element of the actual carrier.

The concrete BN-pair identifies the Weyl quotient with `DihedralGroup 6`;
the arm and central reflections are respectively `sr 0` and `sr 1`. The
hexagonal BN-pair construction then proves the metric and apartment claims
on the original typed left cosets. This includes q = 2 and uses no simplicity,
local normalizer coverage or apartment-fixer hypothesis.

Sources: GLS3 §§2.3 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), the building
geometry used in the finite Borel–Tits argument of Theorem 3.1.3.
-/

public section
noncomputable section
namespace Triality.Standard.TwoLocalGeometry

open Parabolics
open Theory.AlgebraicGroup.TitsSystem

private def nodeEquivBool : Node ≃ Bool where
  toFun
    | .arms => false
    | .central => true
  invFun
    | false => .arms
    | true => .central
  left_inv a := by cases a <;> rfl
  right_inv b := by cases b <;> rfl

/-- The algebraic marking uses the proved concrete Weyl quotient and the
full root parabolics, without any geometric certificate. -/
private def hexagonalDatum (f : ℕ) (hf : 0 < f) :
    HexagonalGeometry.HexagonalDatum (ConcreteBruhat.titsSystem f hf)
      (parabolic (binaryParameters f hf)) where
  typeEquiv := nodeEquivBool
  simple := ConcreteBruhat.simpleReflection f hf
  simple_range := (ConcreteBruhat.titsSystem_S f hf).symm
  weylEquiv := (ConcreteBruhat.weylEquiv f hf).symm
  map_simple a := by
    simp only [ConcreteBruhat.simpleReflection, MulEquiv.symm_apply_apply]
    cases a <;> rfl
  parabolic_eq := ConcreteBruhat.parabolic_eq_standardParabolic f hf

/-- The actual normalizer orbit, not an auxiliary apartment model, is the
support of a simple twelve-cycle in the published incidence graph. -/
theorem standardApartmentCycle (f : ℕ) (hf : 0 < f) :
    ∃ v, ∃ p : (incidenceGraph f hf).Walk v v,
      p.IsCycle ∧ p.length = 12 ∧ {w | w ∈ p.support} = standardApartment f hf :=
  (hexagonalDatum f hf).standardApartmentCycle

/-- The genuine triality parabolic incidence graph has diameter at most six
and every simple cycle has length at least twelve, including at q = 2. -/
theorem hexagonGeometry (f : ℕ) (hf : 0 < f) : HexagonGeometry f hf where
  diameter_bound := HexagonalGeometry.diameter_bound_of_standardApartmentCycle
    _ _ (hexagonalDatum f hf).borel_le (hexagonalDatum f hf).standardApartmentCycle
  cycle_bound := (hexagonalDatum f hf).cycle_bound

/-- Every twelve-cycle is a translate of the standard normalizer apartment
under the action of the original triality carrier. -/
theorem apartmentTranslates (f : ℕ) (hf : 0 < f) : ApartmentTranslates f hf :=
  (hexagonalDatum f hf).apartment_translates_of_cycle_bound
    (hexagonalDatum f hf).standardApartmentCycle (hexagonalDatum f hf).cycle_bound

end Triality.Standard.TwoLocalGeometry
