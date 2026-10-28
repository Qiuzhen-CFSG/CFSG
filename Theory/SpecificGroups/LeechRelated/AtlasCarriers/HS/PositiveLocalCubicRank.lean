module

public import Theory.Quasithin.PositiveLocalRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient

/-!
# Positive two-local cubic rank in Higman--Sims

The literal normalizer of a checked nontrivial elementary two-subgroup
surjects onto S₅. Its order is therefore divisible by three, providing
a local cubic witness without any quotient-rank inference.

This is the local contribution used with the independent ordinary-rank
bound in the nonnormal-component sieve of Aschbacher--Smith A.1.34 and A.3.8.
Source for the literal model witness: Aschbacher--Smith I.4.8, printed p.418; GLS3 Table 5.3m.
-/

public section
open Subgroup Theory.Quasithin

namespace Sporadic.LeechRelated.HS
open EvenLocalCandidates EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient

theorem one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 Carrier := by
  apply one_le_twoLocalPrimeRank_of_dvd_card (localGroup 0)
    ⟨elementary 0, elementary_ne_bot 0, elementary_isPGroup 0, rfl⟩
  have hd := card_dvd_of_surjective fiveHom fiveHom_surjective
  apply dvd_trans (b := Nat.card (Equiv.Perm (Fin 5))) _ hd
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
end Sporadic.LeechRelated.HS
