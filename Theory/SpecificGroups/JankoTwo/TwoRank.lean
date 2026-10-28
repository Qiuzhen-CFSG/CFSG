module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalModel
public import Theory.SpecificGroups.MinusExtraspecial.ElementaryBound
public import Theory.GroupTheory.PrimeRankCoprimeIndex
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# A native two-rank bound for Hall--Janko

The literal first involution centralizer has odd index 315. Its full
two-core is the minus-extraspecial group of order 32, whose elementary
subgroups have order at most four, and its actual quotient is A₅.
The kernel/image inequality bounds this centralizer's two-rank by four;
odd index transfers the bound to the original J₂ carrier.

No elementary-subgroup census of J₂ or stronger rank classification is
assumed. The bound is sufficient for the ordinary component in
Aschbacher--Smith 12.7.5, printed p.840, preserving its full central cover.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics FirstParabolic

/-- The literal first involution centralizer has two-rank at most four. -/
theorem firstCentralizer_primeRank_two_le_four : primeRank 2 Seed.l₁ ≤ 4 := by
  have hcore : primeRank 2 (pCore 2 Seed.l₁) ≤ 2 := by
    apply (primeRank_le_iff_elementary_card_le (pCore 2 Seed.l₁)).mpr
    intro A hA
    exact MinusExtraspecial.elementary_subgroup_card_le_four coreModelEquiv A hA
  have hquot : primeRank 2 (Seed.l₁ ⧸ pCore 2 Seed.l₁) ≤ 2 := by
    rw [primeRank_equiv 2 l₁_quotient.some]
    apply primeRank_le_of_prime_pow_not_dvd
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hr := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' (pCore 2 Seed.l₁))
  rw [QuotientGroup.ker_mk'] at hr
  omega

/-- The actual Hall--Janko carrier has two-rank at most four. -/
theorem primeRank_two_le_four : primeRank 2 Carrier ≤ 4 := by
  have hi : ¬ 2 ∣ Seed.l₁.index := by
    rw [show Seed.l₁.index = 315 from GeneratorPair.FirstFusion.centralizer_index]
    decide
  rw [← Seed.l₁.primeRank_eq_of_not_dvd_index hi]
  exact firstCentralizer_primeRank_two_le_four

end Sporadic.LeechRelated.J2
