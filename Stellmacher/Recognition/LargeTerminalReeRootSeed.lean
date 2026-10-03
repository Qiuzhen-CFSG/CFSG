module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData

/-!
# The cyclic fixed root at the upper terminal endpoint

If the actual five-fixed subgroup of the second core is cyclic of order
four, choose its generator. Its unique involution is the designated
omega-central involution, so the generator squares to that involution.
It lies outside the first residual: a fixed element there is central in
the residual, whose center has order two.

This extracts the candidate for Shinoda's root 5, with root 12 already
specified. No relations with the other eight core roots or the complement
are asserted here. Source: Thompson VI, pp.629–630, and Shinoda (1975),
(2.3), pp.81–82. Cyclicity remains an explicit input.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- A cyclic four-element fixed subgroup has a generator outside the residual
whose square is the designated central involution. -/
public theorem LargeTerminalContext.exists_five_fixed_root_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ t : G, t ∈ twoCoreIn ctx.second ∧ t ∈ centralizer (A : Set G) ∧
      t ∉ ctx.firstResidual ∧ orderOf t = 4 ∧ t ^ 2 = z ∧
      zpowers t = twoCoreIn ctx.second ⊓ centralizer (A : Set G) := by
  let Q := twoCoreIn ctx.second
  let F := (centralizer (A : Set G)).subgroupOf Q
  let _ : IsCyclic F := hcyc
  have hzR : z ∈ ctx.firstResidual := by
    have hZR : omegaOneCenter (S : Subgroup G) ≤ ctx.firstResidual := by
      rw [← ctx.first_residual_center_eq_omegaOneCenter]
      exact map_subtype_le _
    exact hZR (hgen ▸ mem_zpowers z)
  have hzQ : z ∈ Q := by
    obtain ⟨_, _, _, hlo, hhi, _⟩ := ctx.involution_centralizer_core
    exact (hlo.trans hhi) hzR
  have hzA : z ∈ centralizer (A : Set G) := by
    have hAC := ctx.five_le_involution_centralizer A hAN z hz hgen
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hAC ha)
  let zF : F := ⟨⟨z, hzQ⟩, hzA⟩
  have hzF : orderOf zF = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hz
  obtain ⟨t, ht⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  have ht4 : orderOf t = 4 := ht.trans hcard
  have hsq : t ^ 2 = zF := IsCyclic.eq_of_orderOf_eq_two
    (by rw [orderOf_pow, ht4]; decide) hzF
  have htG : orderOf ((t : Q) : G) = 4 := by
    simpa only [orderOf_submonoid] using ht4
  refine ⟨t, t.val.property, t.property, ?_, htG,
    congrArg (fun f : F => ((f : Q) : G)) hsq, ?_⟩
  · intro htR
    let tc : center ctx.firstResidual := ⟨⟨t, htR⟩, hfixed t.property⟩
    have ho : orderOf tc = 4 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact htG
    have hd := orderOf_dvd_natCard tc
    rw [ho, ctx.first_residual_structure.2.2.2.1] at hd
    norm_num at hd

  · have hmap : F.map Q.subtype = Q ⊓ centralizer (A : Set G) := by
      rw [subgroupOf_map_subtype, inf_comm]
    have hFcard : Nat.card (Q ⊓ centralizer (A : Set G) : Subgroup G) = 4 := by
      rw [← hmap, card_map_of_injective Q.subtype_injective]
      exact hcard
    have hle : zpowers ((t : Q) : G) ≤ Q ⊓ centralizer (A : Set G) :=
      zpowers_le.mpr ⟨t.val.property, t.property⟩
    apply eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, htG, hFcard]

end Stellmacher.Recognition
