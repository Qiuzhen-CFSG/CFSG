module

public import Stellmacher.Recognition.FongWreathedDegreeConstraints
public import Stellmacher.Recognition.FongWreathedCyclicQuaternionRestrictions
public import Stellmacher.Recognition.FongWreathedSylowRestrictionSums
public import Theory.Character.IntegralRestriction
public import Theory.Character.RationalPower

/-!
# Restriction congruences for Fong's rational character rows

This module isolates the four restriction congruences in `FongRowConditions`.
The arithmetic assembly takes the integral numerators from the cyclic
subgroup of order eight, the quaternion subgroup of order eight, and the
full Sylow subgroup. The full-Sylow numerators are the pairings with the
principal character and with the linear character `w(F) = I`, `w(E) = -I`.
Their combination gives Fong's pairing with `1 + 3w`.

The character-theoretic calculations supplying these numerators are proved
in the imported cyclic/quaternion and full-Sylow modules. Their assembly here
gives all four congruences for any actual integer-valued character, given the
base orientation. Rational power invariance and the general integrality lemmas
are proved in the imported `Theory` modules. The remaining degree, parity,
and bound conditions stay explicit in the adapter to `FongRowConditions`.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), p. 73, congruences (i)--(iii); and
`refs/original/n-group-global/sylow32-source-audit/fong-degree-calculation-audit.md`
for the full-Sylow principal restriction.
-/

namespace Stellmacher.Recognition

/-- The four congruences needed from restriction for a single character row. -/
public structure FongRestrictionCongruences (r : FongCharacterRow) (f : ℤ) : Prop where
  degree_congr : r.d % 8 = r.a % 8
  orderFour_congr : r.a % 4 = r.b % 4
  restriction_congr : (r.d - 2 * r.a + 7 * r.b + 2 * f) % 8 = 0
  sylow_restriction : (32 : ℤ) ∣ r.d + 7 * r.a + 6 * r.c + 10 * r.b + 8 * f

/-- Combine cyclic, quaternion, and two full-Sylow restriction numerators.
The latter are the pairings with the principal character and with
`w(F) = I`, `w(E) = -I`, respectively. -/
public theorem fongRestrictionCongruences_of_numerators
    (r : FongCharacterRow) (f : ℤ)
    (hC : (8 : ℤ) ∣ r.d - r.a)
    (hQ : (8 : ℤ) ∣ r.d + r.a + 6 * r.b)
    (hS : (32 : ℤ) ∣ r.d + 7 * r.a + 6 * r.c + 10 * r.b + 8 * f)
    (hW : (32 : ℤ) ∣ r.d - 5 * r.a - 2 * r.c + 6 * r.b) :
    FongRestrictionCongruences r f := by
  obtain ⟨u, hu⟩ := hC
  obtain ⟨v, hv⟩ := hQ
  obtain ⟨w, hw⟩ := hW
  refine ⟨?_, ?_, ?_, hS⟩
  · omega
  · omega
  · obtain ⟨s, hs⟩ := hS
    omega

/-- Every actual integer-valued character satisfies Fong's four restriction
congruences for its values at `1`, `J`, `XF²`, `F²`, and `F`. This uses only
the supplied oriented Sylow presentation, with no exceptional-character or
group-order hypothesis. -/
public theorem fongRestrictionCongruences_of_character
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (ho : FongWreathedIntrinsic.BaseOrientation S P)
    {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (r : FongCharacterRow) (f : ℤ)
    (hd : χ 1 = (r.d : ℂ))
    (ha : χ (FongWreathedIntrinsic.J P : S) = (r.a : ℂ))
    (hb : χ (FongWreathedIntrinsic.X P * FongWreathedIntrinsic.F P ^ 2 : S) =
      (r.b : ℂ))
    (hc : χ (FongWreathedIntrinsic.F P ^ 2 : S) = (r.c : ℂ))
    (hf : χ (FongWreathedIntrinsic.F P : S) = (f : ℂ)) :
    FongRestrictionCongruences r f := by
  obtain ⟨hC, hQ⟩ := FongWreathedIntrinsic.cyclic_quaternion_restriction_numerators
    S P ho hχ hint r.d r.a r.b hd ha hb
  obtain ⟨hS, hW⟩ := FongWreathedIntrinsic.RestrictionSums.full_sylow_numerators
    S P ho hχ hint r.d r.a r.b r.c f hd ha hb hc hf
  exact fongRestrictionCongruences_of_numerators r f hC hQ hS hW

/-- Supply the remaining exceptional-character conditions to obtain the full
row interface used by the degree calculation. -/
public theorem FongRestrictionCongruences.toRowConditions
    {r : FongCharacterRow} {f : ℤ} (h : FongRestrictionCongruences r f)
    (degree_gt : |r.a| < r.d) (involution_odd : Odd r.a)
    (involution_bound : |r.a| ≤ 5) (centralFour_bound : |r.c| ≤ 5) :
    FongRowConditions r f where
  degree_gt := degree_gt
  involution_odd := involution_odd
  involution_bound := involution_bound
  degree_congr := h.degree_congr
  orderFour_congr := h.orderFour_congr
  restriction_congr := h.restriction_congr
  centralFour_bound := centralFour_bound
  sylow_restriction := h.sylow_restriction

end Stellmacher.Recognition
