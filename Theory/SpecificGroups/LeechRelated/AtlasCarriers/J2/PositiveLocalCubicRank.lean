module

public import Theory.Quasithin.PositiveLocalRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral

/-!
# Positive two-local cubic rank in Hall--Janko

The checked centralizer of the original involution generator is E₄ × A₅.
Its order is divisible by three, providing a local cubic witness.

This is the local contribution used with the independent ordinary-rank
bound in the nonnormal-component sieve of Aschbacher--Smith A.1.34 and A.3.8.
Source for the literal model witness: Aschbacher--Smith 16.1.5(8), printed p.1172; GLS3 Table 5.3g.
-/

public section
open Subgroup Theory.Quasithin

namespace Sporadic.LeechRelated.J2
open GeneratorPair InnerInvolutionCores

theorem one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 Carrier := by
  have ha : orderOf a = 2 := by
    apply orderOf_eq_prime a_pow_two
    intro h
    have he := congrArg (fun g : Carrier => inclusion g 0) h
    change generatorA 0 = 0 at he
    rw [generatorA_eq_table] at he
    exact (by decide : (83 : Fin 100) ≠ 0) he
  apply one_le_twoLocalPrimeRank_of_dvd_involution_centralizer a ha
  rw [Nat.card_congr a_centralizer_equiv.toEquiv, Nat.card_prod,
    nat_card_alternatingGroup, Nat.card_fin]
  norm_num [E4, C2, Nat.card_fun, Nat.factorial]
end Sporadic.LeechRelated.J2
