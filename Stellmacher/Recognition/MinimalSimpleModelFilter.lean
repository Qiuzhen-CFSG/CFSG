module

public import Stellmacher.Recognition.MinimalSimpleModels
public import Stellmacher.Recognition.MinimalSimpleBasic
public import Stellmacher.Recognition.MinimalSimpleBinaryParameters
public import Stellmacher.Recognition.MinimalSimpleOddParameters
public import Stellmacher.Recognition.MinimalSimpleSuzukiParameters
public import Stellmacher.Recognition.MinimalSimpleUnitaryThree
public import Stellmacher.Recognition.PSL3ThreeModel
public import Stellmacher.Recognition.NGroupReduction
public import Theory.SpecificGroups.AlternatingSevenNotMinimal
public import Theory.Mathieu.M11.Properties.NotMinimalSimple
public import Theory.SpecificGroups.Tits.NotMinimalSimple

/-!
# Filtering recognized models for minimal simple groups

For a group already recognized in the N catalogue, minimal simplicity forces
the prime-exponent and residue conditions in Thompson's five families. The
odd-field parameter theorem includes the actual equivalence from PSL₂(5) to
binary PSL₂(4). The other witnesses are composed with the catalogue's group
equivalences, including the concrete PSL₃(3) transport.

The proper nonsolvable subgroup obstructions exclude A₇, M₁₁, PSU₃(3), and
the Tits presentation. The N₂ version first uses the all-prime N condition
of minimal simplicity to remove the extra even-unitary family. No global
recognition theorem is assumed here.

Source: Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable*, I (1968), Corollary 1, p. 388; the parameter and subgroup
arguments are proved in the imported modules.
-/

namespace Stellmacher.Recognition

universe u
variable {G : Type u} [Group G] [Finite G]

/-- An already recognized minimal simple N-model belongs to Thompson's five
families, with actual multiplicative equivalences. -/
public theorem thompsonMinimalSimpleModel_of_isNGroupModel
    (hG : IsMinimalSimple G) (hmodel : IsNGroupModel G) :
    ThompsonMinimalSimpleModel G := by
  cases hmodel with
  | psl2Even n hn e =>
    exact .psl2Binary n (minimalSimple_binary_branch_prime hn hG e) e
  | psl2Odd K hodd hcard e =>
    rcases minimalSimple_odd_psl2_parameters hodd hcard (hG.of_mulEquiv e) with
      hBinary | hPrime | hThree
    · obtain ⟨f⟩ := hBinary
      exact .psl2Binary 2 (by decide) (e.trans f)
    · obtain ⟨p, hp, hgt, hmod, ⟨f⟩⟩ := hPrime
      let _ : Fact p.Prime := hp
      exact .psl2Prime p hp.out hgt hmod (e.trans f)
    · obtain ⟨p, hp, hodd, ⟨f⟩⟩ := hThree
      exact .psl2ThreePower p hp hodd (e.trans f)
  | suzuki n hn e =>
    exact .suzuki n (minimalSimple_suzuki_branch_prime hn hG e) e
  | alternatingSeven e =>
    exact (alternatingGroup.not_isMinimalSimple_seven (hG.of_mulEquiv e)).elim
  | mathieuEleven e =>
    exact (Sporadic.Mathieu.m11_not_isMinimalSimple (hG.of_mulEquiv e)).elim
  | linearThree h =>
    obtain ⟨e⟩ := ABG.isPSL3_three_iff_nonempty_mulEquiv.mp h
    exact .psl3Three e
  | unitaryThree h =>
    exact (not_isPSU3_three_of_isMinimalSimple hG h).elim
  | tits e =>
    exact (Tits.not_mulEquiv_parrottGroup hG e).elim

/-- The N₂ catalogue has the same five minimal-simple possibilities, since
minimal simplicity also supplies the all-prime N condition. -/
public theorem thompsonMinimalSimpleModel_of_isNTwoGroupModel
    (hG : IsMinimalSimple G) (hmodel : IsNTwoGroupModel G) :
    ThompsonMinimalSimpleModel G :=
  thompsonMinimalSimpleModel_of_isNGroupModel hG
    (isNGroupModel_of_isNTwoGroupModel hG.isNGroup hmodel)

end Stellmacher.Recognition
