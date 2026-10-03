module

public import Stellmacher.Recognition.Parrott.SylowBWQuadraticInputs
public import Theory.GroupTheory.ElementarySecondCenterSquareQuadratic

/-!
# Quadraticity of the actual Parrott core square map

The derived subgroup of the core is elementary abelian and equals its second
center; the abelianization is elementary abelian too. Thus the general
seven-term identity applies to every square map with the literal evaluation
on core representatives. No choice of action or Sylow frame is required.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, the core quadratic structure used on p.678.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
local notation "J" => pCore 2 H
local notation "D" => commutator J
set_option quotPrecheck false in
local notation "Z" => (center J).subgroupOf D
local notation "V" => J ⧸ D
local notation "W" => D ⧸ Z

/-- Literal core squares satisfy the seven-term quadratic identity. -/
public theorem parrott_core_square_seven_term
    (h : ParrottCentralizerHypotheses z) (square : V → W)
    (hsquare : ∀ (j : J) (hj : j ^ 2 ∈ D),
      square (QuotientGroup.mk' D j) = QuotientGroup.mk' Z ⟨j ^ 2, hj⟩)
    (a b c : V) :
    square (a * b * c) * square (a * b) * square (a * c) * square (b * c) *
      square a * square b * square c = 1 := by
  obtain ⟨_, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  have hsq (j : J) : j ^ 2 ∈ D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' D (j ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (parrott_core_abelianization_structure z h).1.exponent_dvd_p
      (QuotientGroup.mk' D j)
  exact square_seven_term_of_evaluation D hUpper.le hsq le_rfl square hsquare a b c

end Stellmacher.Recognition
