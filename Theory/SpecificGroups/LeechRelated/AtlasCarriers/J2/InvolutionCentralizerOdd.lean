module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Odd divisors in Hall--Janko involution centralizers

The certified carrier involution fusion reduces to the two representative
centralizers, of orders 240 and 1920. Conjugation preserves their orders, so
every involution centralizer has order divisible by three and cannot be a
two-group. This uses no condition on a chosen Sylow subgroup.

Source: GLS3 Table 5.3g, classes 2A and 2B, via the retained ATLAS J2G1-p100B0
certificates. The one-centralizer exclusion is used in Aschbacher--Smith G.4.1.
-/

public section
namespace Sporadic.LeechRelated.J2
open Subgroup InnerInvolutionCores ExceptionalParabolics GeneratorPair

private theorem centralizer_card_eq_of_isConj {x y : Carrier} (h : IsConj x y) :
    Nat.card (centralizer ({y} : Set Carrier)) =
      Nat.card (centralizer ({x} : Set Carrier)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he : MulAut.conj y = MulAut.congr (MulAut.conj g) (MulAut.conj x) := by
    rw [MulAut.congr_conj]
    exact congrArg MulAut.conj hg.symm
  rw [← MulAut.fixedSubgroup_conj, ← MulAut.fixedSubgroup_conj, he]
  exact (Nat.card_congr (MulAut.fixedSubgroupCongr (MulAut.conj g)
    (MulAut.conj x)).toEquiv).symm

/-- Every involution centralizer in the actual J₂ carrier has an odd prime divisor. -/
theorem three_dvd_card_involution_centralizer (i : Carrier) (hi : orderOf i = 2) :
    3 ∣ Nat.card (centralizer ({i} : Set Carrier)) := by
  rcases involution_fusion i hi with h | h
  · rw [centralizer_card_eq_of_isConj h, Nat.card_congr a_centralizer_equiv.toEquiv,
      Nat.card_prod, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [E4, C2, Nat.card_fun, Nat.factorial]
  · rw [centralizer_card_eq_of_isConj h]
    change 3 ∣ Nat.card Seed.l₁
    rw [FirstParabolic.card_l₁]
    decide

/-- No involution in the actual J₂ carrier has a two-group centralizer. -/
theorem not_isPGroup_involution_centralizer (i : Carrier) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set Carrier)) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
  have hd := Nat.prime_three.dvd_of_dvd_pow
    ((three_dvd_card_involution_centralizer i hi).trans hn)
  norm_num at hd

end Sporadic.LeechRelated.J2
