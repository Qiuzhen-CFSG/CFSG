module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five.Order
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five.PermutationLift

/-!
# Odd central closure of the actual SU₅(4) matrix group

The exact group and monomial subgroup orders and the permutation-equivariant
five-torus lift discharge the remaining odd-primary section premises. Prime
kernel reduction then excludes every odd prime from every perfect central
covering kernel. Thus each such kernel is a two-group. This is sufficient
for the original A.2.18 source group, whose two-core is trivial; no assertion
about defining-primary closure is required here.

Source: Aschbacher--Smith A.2.18 and I.1.4(4), printed pp.40 and 408;
GLS3 Section 6.1.
-/

public section
open BenderSuzuki.MatrixGroups PerfectCentralCovering
open HermitianForm.IdentityGram
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure
universe u
variable {F : Type u} [Field F] [Finite F]

/-- All odd-prime local sections of the identity-form SU₅(4) model are proved. -/
theorem odd_primeLocalSections_four (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → PrimeLocalSections J p := by
  let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
  apply odd_primeLocalSections_of_card_dvd_and_five J hcard hconj hJ
    (OddSections.card_specialSubgroup_dvd J hcard hconj hJ)
  apply OddSections.five_primeLocalSections_of_monomial_card_and_permutation_lifts
    J hJ hconj (OddSections.Five.card_monomial J hJ hconj hcard)
    (OddSections.card_specialSubgroup_dvd J hcard hconj hJ)
  intro E _ _ d hd
  exact OddSections.Five.hasPermutationTorusLift_of_kernel_card_five J hJ hconj hcard d hd

/-- Every perfect central cover of the literal SU₅(4) group has two-group kernel. -/
theorem kernel_isTwoGroup_four (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    {E : Type u} [Group E] [Finite E] (c : Cover E J.specialSubgroup) :
    IsPGroup 2 c.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
  have he : p = 2 := by
    by_contra hp2
    let : Fact p.Prime := ⟨hpp⟩
    exact not_dvd_kernel_of_identity_prime_sections J hcard hconj
      (odd_primeLocalSections_four (identityGram J) hcard hconj rfl p hpp hp2) c hpd
  norm_num [he]

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure
