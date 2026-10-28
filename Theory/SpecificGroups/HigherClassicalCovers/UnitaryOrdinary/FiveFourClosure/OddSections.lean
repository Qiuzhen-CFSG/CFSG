module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Cyclic
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Three

/-!
# Odd-prime local sections for SU₅(4): assembly

The natural matrix representation excludes all kernel primes other than
2, 3, 5 and 17. The actual plane Levi supplies the three-primary torus
calculation; the expected unitary order bound also excludes 17².
Thus only that independent order bound and the five-primary local section
remain as premises. The five-primary Sylow subgroup is nonabelian and is
not covered by the cyclic argument.

The last theorem applies these calculations to the normalized matrix group
and the literal covering map in `injective_of_identity_primary_sections`.
This is a conditional assembly, not a proof of central closure or the
source multiplier formula until its order and five-primary inputs are proved.

Source: Aschbacher--Smith I.1.4(4), printed p.408 of `refs/quasithin.pdf`,
and GLS3 Section 6.1. Final arbitrary-form universality belongs to the parent.
-/

public section
open BenderSuzuki.MatrixGroups PerfectCentralCovering
open HermitianForm.IdentityGram

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure

universe u
variable {F : Type u} [Field F] [Finite F]

/-- The remaining order and five-primary inputs assemble all odd-prime sections.
The three-primary and all cyclic branches are discharged by actual matrix calculations. -/
theorem odd_primeLocalSections_of_card_dvd_and_five
    (J : HermitianForm 5 F) (hF : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4) (hJ : J.form = 1)
    (hG : Nat.card J.specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41)
    (hfive : PrimeLocalSections J 5) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → PrimeLocalSections J p := by
  intro p hp hp2
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp3 : p = 3
  · subst p
    exact OddSections.three_primeLocalSections_of_card_dvd J hF hconj hJ hG
  by_cases hp5 : p = 5
  · subst p
    exact hfive
  by_cases hp17 : p = 17
  · subst p
    exact OddSections.seventeen_primeLocalSections_of_card_dvd J hG
  exact OddSections.primeLocalSections_of_ne_two_three_five_seventeen
    J hF hp2 hp3 hp5 hp17

/-- Application to the literal covering map over an arbitrary original form.
Its normalized odd-prime premise is reduced to the independent order and
five-primary calculations; the defining-prime calculation remains with its owner. -/
theorem injective_of_identity_card_five_two_sections
    (J : HermitianForm 5 F) (hF : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x^4)
    (hG : Nat.card (identityGram J).specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41)
    (hfive : PrimeLocalSections (identityGram J) 5)
    (htwo : PrimeLocalSections (identityGram J) 2)
    {E : Type u} [Group E] [Finite E] (d : Cover E J.specialSubgroup) :
    Function.Injective d.toMonoidHom := by
  exact injective_of_identity_primary_sections J hF hconj htwo
    (odd_primeLocalSections_of_card_dvd_and_five (identityGram J)
      hF hconj rfl hG hfive) d

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure
