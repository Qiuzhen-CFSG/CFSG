module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# Quasisimple subgroups in a central product of full prime rank

A normal quasisimple factor with p-prime center and full ambient p-rank has
p-prime centralizer. Its central-product quotient therefore has p-prime order.
A quasisimple subgroup whose simple quotient has order divisible by p lies
inside that factor. Equal central-quotient orders force equality of the
whole perfect covers, using their actual inclusions and central kernels.

Application: preserving the J₄ covering component when reselecting an
involution-centralizer overgroup in Aschbacher--Smith 4.2.13, printed p.612.
-/

public noncomputable section

namespace Theory.GroupTheory
open Subgroup ResidualCentralizerRank
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A quasisimple subgroup cannot survive in a quotient of prime-to-p order
when p divides the order of its simple central quotient. -/
theorem quasisimple_le_normal_of_prime_to_index {p : ℕ}
    (K N : Subgroup G) [IsQuasisimple K] [N.Normal]
    (hd : p ∣ Nat.card (K ⧸ center K)) (hi : ¬ p ∣ N.index) : K ≤ N := by
  let f := (QuotientGroup.mk' N).comp K.subtype
  rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hk | ht
  · have hd' : p ∣ Nat.card f.range := by
      rw [←index_ker]
      exact hd.trans (index_dvd_of_le hk)
    exact (hi (hd'.trans (card_subgroup_dvd_card f.range))).elim
  · intro k hk
    exact (QuotientGroup.eq_one_iff k).mp
      (MonoidHom.mem_ker.mp (show (⟨k,hk⟩ : K) ∈ f.ker from ht ▸ mem_top _))

/-- Contained quasisimple groups with isomorphic simple central quotients
coincide. The whole central covers are retained. -/
theorem quasisimple_eq_of_le_of_center_quotient_card
    (K N : Subgroup G) [IsQuasisimple K] [IsQuasisimple N]
    (hKN : K ≤ N)
    (hc : Nat.card (K ⧸ center K) = Nat.card (N ⧸ center N)) : K = N := by
  let f := (QuotientGroup.mk' (center N)).comp (inclusion hKN)
  have hk : f.ker ≤ center K := by
    intro k hk
    have hz : inclusion hKN k ∈ center N := (QuotientGroup.eq_one_iff _).mp hk
    exact mem_center_iff.mpr fun l => (inclusion_injective hKN) (by
      simpa only [map_mul] using mem_center_iff.mp hz (inclusion hKN l))
  have hd : Nat.card (N ⧸ center N) ∣ Nat.card f.range := by
    rw [←hc,←index_ker]
    exact index_dvd_of_le hk
  have hf : f.range = ⊤ := f.range.eq_top_of_card_eq
    (le_antisymm (card_le_card_group _) (Nat.le_of_dvd Nat.card_pos hd))
  have hmap : (K.subgroupOf N).map (QuotientGroup.mk' (center N)) = ⊤ := by
    rw [←hf]
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
    · rintro ⟨k,rfl⟩
      exact ⟨inclusion hKN k,k.property,rfl⟩
  have htop : (⊤ : Subgroup N) ≤ K.subgroupOf N :=
    Subgroup.le_of_map_le_of_perfect (QuotientGroup.mk' (center N))
      (by rw [QuotientGroup.ker_mk']) ⊤ (K.subgroupOf N) (by rw [hmap]; exact le_top)
  exact le_antisymm hKN (fun x hx => htop (show (⟨x,hx⟩ : N) ∈ ⊤ from mem_top _))

/-- In a central product, a full-rank normal quasisimple factor contains
every quasisimple subgroup with the same central quotient. -/
theorem quasisimple_eq_of_full_rank_central_product {p n : ℕ} [Fact p.Prime]
    (K N : Subgroup G) [IsQuasisimple K] [IsQuasisimple N] [N.Normal]
    (hprod : N ⊔ centralizer (N : Set G) = ⊤)
    (hz : Nat.Coprime p (Nat.card (center N)))
    (hr : n ≤ primeRank p N) (hG : primeRank p G ≤ n)
    (hd : p ∣ Nat.card (K ⧸ center K))
    (hc : Nat.card (K ⧸ center K) = Nat.card (N ⧸ center N)) : K = N := by
  let C := centralizer (N : Set G)
  have hadd := primeRank_add_le_of_center_coprime C N le_rfl hz
  have hzero : primeRank p C = 0 := by omega
  have hC : ¬ p ∣ Nat.card C := PrimeRank.eq_zero_iff_not_dvd_card.mp hzero
  have hs : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨a,ha,c,hc,rfl⟩ := mem_sup_of_normal_left.mp (hprod ▸ mem_top g)
    refine ⟨⟨c,hc⟩,?_⟩
    change QuotientGroup.mk' N c = QuotientGroup.mk' N (a*c)
    have ha1 : QuotientGroup.mk' N a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [map_mul,ha1,one_mul]
  have hi : ¬ p ∣ N.index := fun hp => hC (hp.trans (card_dvd_of_surjective _ hs))
  exact quasisimple_eq_of_le_of_center_quotient_card K N
    (quasisimple_le_normal_of_prime_to_index K N hd hi) hc
end Theory.GroupTheory
