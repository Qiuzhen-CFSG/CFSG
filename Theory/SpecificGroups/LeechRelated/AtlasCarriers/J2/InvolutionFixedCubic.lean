module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCores
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.PermutationComparison

/-!
# The actual Hall--Janko component cannot occur in the source sieve

The certified two inner involution centralizers have orders 240 and 1920;
the certified outer involution fixed group has order 336. Thus every
involutory automorphism of the actual carrier fixes an element of order three.
The marked automorphism transports this fixed element to the original ambient
centralizer, contradicting the source's order-prime-to-three hypothesis.

Source: GLS3, Table 5.3g; Aschbacher--Smith, 15.3.58, printed p.1149.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.J2
open InnerInvolutionCores ExceptionalParabolics GeneratorPair

/-- Every involutory automorphism of the actual Hall--Janko group fixes a cubic. -/
theorem exists_fixed_cubic_of_involution (a : MulAut Carrier) (ha : orderOf a = 2) :
    ∃ d : Carrier, orderOf d = 3 ∧ a d = d := by
  classical
  have hc : 3 ∣ Nat.card a.fixedSubgroup := by
    by_cases hi : a ∈ (MulAut.conj : Carrier →* MulAut Carrier).range
    · obtain ⟨g, hg⟩ := hi
      rcases InnerInvolutionCores.inner_fixed_representatives a ha ⟨g, hg.symm⟩ with he | he
      · obtain ⟨e⟩ := he
        rw [Nat.card_congr e.toEquiv,
          Nat.card_congr a_centralizer_equiv.toEquiv, Nat.card_prod,
          nat_card_alternatingGroup, Nat.card_fin]
        norm_num [E4, C2, Nat.card_fun, Nat.factorial]
      · obtain ⟨e⟩ := he
        rw [Nat.card_congr e.toEquiv]
        change 3 ∣ Nat.card Seed.l₁
        rw [FirstParabolic.card_l₁]
        decide
    · obtain ⟨e, he⟩ := isConj_iff.mp (OuterInvolutionCores.outer_involution_fusion a ha hi)
      have heq : a = MulAut.congr e involutionAut := by
        rw [← he]
        rfl
      rw [heq, ← Nat.card_congr (MulAut.fixedSubgroupCongr e involutionAut).toEquiv,
        OuterInvolutionCentralizer.card_fixed]
      decide
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := a.fixedSubgroup) 3 hc
  exact ⟨d, (Subgroup.orderOf_coe d).trans hd, (MulAut.mem_fixedSubgroup a d).mp d.property⟩

end Sporadic.LeechRelated.J2

