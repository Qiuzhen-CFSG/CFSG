module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction.Survivors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction.RankInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction.SignedRanks
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction.DerivedRanks

/-!
# Higher-field model reduction for the external cubic branch

The surviving actual carriers are centerless, have order divisible by three,
and have special matrix realizations with the same parameters. These facts
are proved in `ModelReduction.Survivors`.

The reduction covers every member of `HigherFieldCarrier`, including the
source congruence on the special covers. Concrete rank-two witnesses exclude
the other signed degree-three parities and the actual derived symplectic and
G₂ carriers. The two witness families are constructed in `SignedRanks` and
`DerivedRanks`, so `HigherFieldCarrier.toExternal` requires only the full
higher-field list and the bound of one on three-rank.

`HigherFieldCarrier.external_structure` also supplies centerlessness,
three-divisibility, and equality in that rank bound. The source owner applies
these intrinsic conclusions to K* and supplies its rank bound separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20(a), printed p.954 (PDF p.971).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
open Chapter1.Section02.LocalModels
open ModelReduction
universe u
variable {D : Type u} [Group D] [Finite D]

/-- Conditional assembly of the full seven-entry higher-field sieve.
`HigherFieldCarrier.toExternal` supplies both concrete matrix-rank inputs. -/
theorem HigherFieldCarrier.toExternal_of_rank_witnesses
    (hsigned : SignedThreeRanks) (hderived : DerivedRanks)
    (h : HigherFieldCarrier D) (hr : primeRank 3 D ≤ 1) : ExternalCarrier D := by
  cases h with
  | linearTwo n hn iso => exact .linearTwo n hn iso
  | projectiveThree unitary n hn iso =>
      cases unitary with
      | false =>
          change ClassicalGroup.IsPSL D 3 (2 ^ n) at iso
          rcases Nat.even_or_odd n with he | ho
          · obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
            have hl := hsigned.linear_projective F n hn hF he
            rw [← primeRank_equiv 3 e] at hl
            omega
          · exact .linearThree n hn ho iso
      | true =>
          change ClassicalGroup.IsPSU D 3 (2 ^ n) at iso
          rcases Nat.even_or_odd n with he | ho
          · exact .unitaryThree n hn he iso
          · obtain ⟨F, hfield, hfin, J, hF, hconj, ⟨e⟩⟩ := iso
            let := Finite.of_equiv D e.toEquiv
            have hl := hsigned.unitary_projective F J n hn hF hconj ho
            rw [← primeRank_equiv 3 e] at hl
            omega
  | specialThree unitary n hn hm iso =>
      have hp := Nat.BinaryTorusParity.two_pow_mod_three n
      cases unitary with
      | false =>
          have he : Even n := by
            simp only [Bool.false_eq_true, if_false] at hm
            rw [Nat.even_iff]
            split_ifs at hp <;> omega
          obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
          have hl := hsigned.linear_special F n hn hF he
          rw [← primeRank_equiv 3 e] at hl
          omega
      | true =>
          have ho : Odd n := by
            simp only [if_true] at hm
            rw [Nat.odd_iff]
            split_ifs at hp <;> omega
          obtain ⟨F, hfield, hfin, J, hF, hconj, ⟨e⟩⟩ := iso
          have hl := hsigned.unitary_special F J n hn hF hconj ho
          rw [← primeRank_equiv 3 e] at hl
          omega
  | symplectic n hn iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      have hl := hderived.symplectic F n hn hF
      rw [← primeRank_equiv 3 e] at hl
      omega
  | g2 n hn iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      have hl := hderived.g2 F n hn hF
      rw [← primeRank_equiv 3 e] at hl
      omega

/-- All intrinsic conclusions required by the external cubic consumer,
with the two concrete rank-witness families left as explicit inputs. -/
theorem HigherFieldCarrier.external_structure_of_rank_witnesses
    (hsigned : SignedThreeRanks) (hderived : DerivedRanks)
    (h : HigherFieldCarrier D) (hr : primeRank 3 D ≤ 1) :
    ExternalCarrier D ∧ center D = ⊥ ∧ 3 ∣ Nat.card D ∧ primeRank 3 D = 1 := by
  have he := h.toExternal_of_rank_witnesses hsigned hderived hr
  exact ⟨he, he.center_eq_bot, he.three_dvd_card, he.threeRank_eq_one hr⟩

/-- Three-rank at most one reduces the full seven-entry higher-field list
to L₂(2ⁿ), L₃(2ⁿ) with odd n > 1, or U₃(2ⁿ) with even n > 1.
Both concrete rank-witness families are discharged here. -/
theorem HigherFieldCarrier.toExternal
    (h : HigherFieldCarrier D) (hr : primeRank 3 D ≤ 1) : ExternalCarrier D :=
  h.toExternal_of_rank_witnesses signedThreeRanks derivedRanks hr

/-- The intrinsic model conclusions in 13.8.20(a), with no additional
rank-witness, centerlessness, or divisibility assumptions. -/
theorem HigherFieldCarrier.external_structure
    (h : HigherFieldCarrier D) (hr : primeRank 3 D ≤ 1) :
    ExternalCarrier D ∧ center D = ⊥ ∧ 3 ∣ Nat.card D ∧ primeRank 3 D = 1 := by
  have he := h.toExternal hr
  exact ⟨he, he.center_eq_bot, he.three_dvd_card, he.threeRank_eq_one hr⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure

end
