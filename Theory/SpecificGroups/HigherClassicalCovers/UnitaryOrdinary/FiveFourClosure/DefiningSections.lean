module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections.Index
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections.Levi

/-!
# Reduction of SU₅(4) defining-prime sections to the line-radical lift

The actual radical–SU₃ subgroup has odd index, and the SU₃ Levi lifts through
every finite central double cover. A compatible lift of the line radical
then multiplies with that Levi lift to give a section of the literal cover
on this actual subgroup. The final theorem applies this construction to the
identity-Gram model and the original covering map via the established form
transport and prime-kernel reduction.

The compatible radical lift remains explicit. Thus these results do not yet
discharge the defining-prime premise of Aschbacher–Smith I.1.4(4), printed
p.408 of `refs/quasithin.pdf`, citing GLS3 §6.1. The scalar-kernel and odd-prime
calculations are not used as substitutes for this missing coordinate proof.
-/

public section

open BenderSuzuki.MatrixGroups Theory.GroupTheory PerfectCentralCovering
open Theory.SpecificGroups.UnitaryFive
open LineCore LineCore.Parabolic HermitianForm.IdentityGram

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure

universe u
variable {F : Type u} [Field F] [Finite F] [CharP F 2]

open DefiningSections

/-- The odd-index and Levi-lifting obligations are discharged. Only the
compatible matrix-radical lift remains in this local-section reduction. -/
theorem primeLocalSections_two_of_radical_lifts (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (hradical : ∀ (E : Type u) [Group E] [Finite E] (d : Cover E J.specialSubgroup),
      Nat.card d.toMonoidHom.ker = 2 →
      ∀ l : (middleForm J).specialSubgroup →* E,
        d.toMonoidHom.comp l = leviSU J hJ →
          HasCompatibleRadicalLift J hJ d.toMonoidHom l) :
    PrimeLocalSections J 2 := by
  intro E _ _ d hd
  obtain ⟨l, hl⟩ := exists_levi_lift J hcard hconj hJ d hd
  obtain ⟨r, hr, heq⟩ := hradical E d hd l hl
  obtain ⟨s, hs⟩ := exists_block_section_of_compatible_lifts J hJ d.toMonoidHom
    r l hr hl heq
  exact ⟨blockSubgroup J hJ, s, blockSubgroup_index_odd J hcard hconj hJ, hs⟩

/-- Apply the local matrix calculation to the normalized model and then to
the literal cover of the original form, with arbitrary central kernel size. -/
theorem not_two_dvd_kernel_of_identity_radical_lifts (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hradical : ∀ (D : Type u) [Group D] [Finite D]
      (d : Cover D (identityGram J).specialSubgroup),
      Nat.card d.toMonoidHom.ker = 2 →
      ∀ l : (middleForm (identityGram J)).specialSubgroup →* D,
        d.toMonoidHom.comp l = leviSU (identityGram J) rfl →
          HasCompatibleRadicalLift (identityGram J) rfl d.toMonoidHom l)
    {E : Type u} [Group E] [Finite E] (c : Cover E J.specialSubgroup) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact not_dvd_kernel_of_identity_prime_sections J hcard hconj
    (primeLocalSections_two_of_radical_lifts (identityGram J) hcard hconj rfl hradical) c

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure
