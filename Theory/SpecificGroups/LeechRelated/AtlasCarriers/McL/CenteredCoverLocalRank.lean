module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeCoverLocalLifts
public import Theory.Quasithin.CentralThreeLocalRank
public import Theory.Quasithin.CoprimeLocalRank
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore

/-!
# Local three-rank in every McLaughlin cover with a central cubic

Quotient a quasisimple cover by its prime-to-three core. That core is
central, and the literal quotient retains both the McL central quotient
and a nontrivial central three-group. The checked McL elementary-nine
lift then forces local three-rank at least three. The coprime-kernel
local-rank inequality transfers this bound back to the original full
cover; no multiplier calculation or arbitrary quotient monotonicity is
needed.

This supplies the McL exclusion for the original exterior cubic in
Hall.OddNormalizer.PushingUpComponentEquality.
Source: Aschbacher--Smith A.2.19, printed p.41; 4.2.13, p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace Sporadic.LeechRelated.McL
variable {G : Type*} [Group G] [Finite G] [IsQuasisimple G]

/-- A central cubic forces two-local three-rank at least three in the full cover. -/
theorem local_three_rank_of_center_divisible
    (h3 : 3 ∣ Nat.card (center G)) (e : G ⧸ center G ≃* Carrier) :
    3 ≤ twoLocalPrimeRank 3 G := by
  classical
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsSimpleGroup Carrier := e.symm.isSimpleGroup
  let N := pPrimeCore 3 G
  have hN : N ≤ center G := by
    rcases IsQuasisimple.normal_le_center_or_eq_top N with hc | ht
    · exact hc
    · have hh := pPrimeCore_coprime_card (p := 3) (G := G)
      change Nat.Coprime 3 (Nat.card N) at hh
      rw [ht,Subgroup.card_top] at hh
      exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3)
        dvd_rfl (h3.trans (card_subgroup_dvd_card _)) hh).elim
  let Q := G ⧸ N
  let π : G →* Q := QuotientGroup.mk' N
  let c : Cover G Q := {
    toMonoidHom := π
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := by rw [QuotientGroup.ker_mk']; exact hN }
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective c.surjective
  let a : Q ⧸ center Q ≃* Carrier := c.quotientCenterEquiv.symm.trans e
  let : IsQuasisimple Q := ⟨a.isSimpleGroup⟩
  have hc : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_coprime_card
  have hZ : IsPGroup 3 (center Q) := by
    rw [IsQuasisimple.center_eq_pCore (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 3))]
    exact pCore_isPGroup
  have hne : center Q ≠ ⊥ := by
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) 3 h3
    have hzG : orderOf (z : G) = 3 := (orderOf_coe z).trans hz
    have hzQ : π (z : G) ∈ center Q := by
      exact (show (z : G) ∈ (center Q).comap π from by
        rw [show (center Q).comap π = center G from c.comap_center]
        exact z.property)
    intro hb
    have hzk : (z : G) ∈ π.ker := by
      change π (z : G) = 1
      simpa only [hb,mem_bot] using hzQ
    have hd : 3 ∣ Nat.card π.ker := by
      have hh := orderOf_dvd_natCard (⟨z,hzk⟩ : π.ker)
      rwa [←orderOf_coe,hzG] at hh
    exact Nat.prime_three.coprime_iff_not_dvd.mp hc hd
  obtain ⟨U,f,hU,hUp,hf,hn⟩ := exists_three_cover_local_lift hZ hne a
  have hr := Theory.Quasithin.three_le_twoLocalPrimeRank_of_injective_central_projection
    hZ hne U hUp hU f hf hn
    (show ∀ a : Multiplicative (ZMod 3 × ZMod 3), a ^ 3 = 1 from by decide)
    (show Nat.card (Multiplicative (ZMod 3 × ZMod 3)) = 3 ^ 2 from by
      rw [Nat.card_congr Multiplicative.toAdd,Nat.card_prod]
      norm_num [Nat.card_zmod])
  exact hr.trans (twoLocalPrimeRank_le_of_surjective_of_coprime 3 π c.surjective hc)

end Sporadic.LeechRelated.McL
