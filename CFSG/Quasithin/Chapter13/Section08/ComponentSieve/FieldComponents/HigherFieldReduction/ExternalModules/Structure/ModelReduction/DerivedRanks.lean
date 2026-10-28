module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction.RankInputs
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Derived-group three-rank witnesses for the higher-field sieve

The field cardinality supplies characteristic two. The binary witness theorem
then gives rank at least two in the actual derived Sp₄ and split-octonion G₂
carriers, discharging both fields of the published `DerivedRanks` contract.

Source: Aschbacher–Smith, proof of 13.8.20(a), printed p.954 (PDF p.971).
-/

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction

/-- Unconditional derived-carrier rank input for the higher-field reduction. -/
public theorem derivedRanks : DerivedRanks := by
  constructor
  · intro F _ _ n _ hF
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
  · intro F _ _ n _ hF
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction
