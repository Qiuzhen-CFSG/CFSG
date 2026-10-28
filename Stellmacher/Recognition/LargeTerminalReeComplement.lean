module

public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Stellmacher.Recognition.LargeTerminalFiveLocalAutomorphisms
public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Stellmacher.Recognition.LargeTerminalReeNormalizerLift
public import Theory.GroupTheory.SpecificGroups.FiveFourComplement

/-!
# Assembly of an actual terminal Frobenius complement

Actual generators of orders five and four satisfying the squaring action
embed the faithful five-by-four group. Its image avoids the two-core;
the known centralizer and core orders then give complementarity.
Centralizing the cyclic fixed root makes the entire image centralize
the fixed subgroup.

The compatible normalizer-lift theorem supplies the order-four generator
by the fixed-root and nonsplit-extension calculations. The final theorem
therefore discharges the generator input without inferring splitting from
the quotient's order or isomorphism type.

Source: Thompson VI, pp.629–630, and Shinoda (1975), pp.81–83.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- Assemble the required complement from actual compatible generators. -/
public theorem LargeTerminalContext.ree_complement_of_generators
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (A : Subgroup G) (c a : centralizer ({z} : Set G))
    (hc : orderOf c = 5) (ha : orderOf a = 4)
    (hconj : a * c * a⁻¹ = c ^ 2) (hA : zpowers (c : G) = A)
    (t : G)
    (ht : zpowers t = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (hct : Commute (c : G) t) (hat : Commute (a : G) t) :
    ∃ j : FiveFour.Group →* centralizer ({z} : Set G),
      Function.Injective j ∧
      j.range.IsComplement' (pCore 2 (centralizer ({z} : Set G))) ∧
      zpowers ((j FiveFour.c : centralizer ({z} : Set G)) : G) = A ∧
      ∀ g, ((j g : centralizer ({z} : Set G)) : G) ∈
        centralizer (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) := by
  let C := centralizer ({z} : Set G)
  have hc5 : c ^ 5 = 1 := hc ▸ pow_orderOf_eq_one c
  have ha4 : a ^ 4 = 1 := ha ▸ pow_orderOf_eq_one a
  let j := FiveFour.lift c a hc5 ha4 hconj
  have hj : Function.Injective j := FiveFour.lift_injective c a hc5 ha4 hconj hc ha
  have hC : Nat.card C = 20480 := by
    change Nat.card (centralizer ({z} : Set G)) = 20480
    rw [ctx.involution_centralizer_eq_second hS z hz hgen]
    exact ctx.second_card_of_large_card hS
  refine ⟨j, hj, ?_, ?_, ?_⟩
  · apply FiveFour.isComplement_range_of_normal_two_subgroup j hj _ pCore_isPGroup
    rw [(ctx.involution_centralizer_core_eq_at_generator hS z hgen).2, hC]
  · simpa only [j, FiveFour.lift_c] using hA
  · intro g
    have hcC : (c : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr hct.eq
    have haC : (a : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr hat.eq
    have hgC : ((j g : C) : G) ∈ centralizer ({t} : Set G) := by
      rw [← FiveFour.normal_form g, map_mul, map_pow, map_pow]
      simp only [j, FiveFour.lift_c, FiveFour.lift_a]
      change (c : G) ^ g.left.toAdd.val * (a : G) ^ g.right.toAdd.val ∈ _
      exact mul_mem (pow_mem hcC _) (pow_mem haC _)
    change ((j g : C) : G) ∈ centralizer
      ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G)
    rw [← ht, zpowers_eq_closure, centralizer_closure]
    exact hgC

/-- Once the squaring element has order four and centralizes the fixed
subgroup, the prescribed five-subgroup and fixed-root data finish assembly. -/
public theorem LargeTerminalContext.ree_complement_of_compatible_squaring_element
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (a : centralizer ({z} : Set G)) (ha : orderOf a = 4)
    (hsquare : ∀ c ∈ A, (a : G) * c * (a : G)⁻¹ = c ^ 2)
    (hafixed : (a : G) ∈ centralizer
      (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G)) :
    ∃ j : FiveFour.Group →* centralizer ({z} : Set G),
      Function.Injective j ∧
      j.range.IsComplement' (pCore 2 (centralizer ({z} : Set G))) ∧
      zpowers ((j FiveFour.c : centralizer ({z} : Set G)) : G) = A ∧
      ∀ g, ((j g : centralizer ({z} : Set G)) : G) ∈
        centralizer (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic A)
  have hcG : orderOf (c : G) = 5 := by
    rw [orderOf_submonoid]
    exact hc.trans hA
  have hcgen : zpowers (c : G) = A := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    rw [Nat.card_zpowers, hcG, hA]
  have hAC : A ≤ centralizer ({z} : Set G) := by
    rw [ctx.involution_centralizer_eq_second hS z hz hgen]
    exact hAP
  let cC : centralizer ({z} : Set G) := ⟨c, hAC c.property⟩
  have hcC : orderOf cC = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hcG
  obtain ⟨t, _, htA, _, _, _, ht⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  apply ctx.ree_complement_of_generators hS z hz hgen A cC a hcC ha
    (Subtype.ext (hsquare c c.property)) hcgen t ht
  · exact mem_centralizer_iff.mp htA c c.property
  · have htmem : t ∈ (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) :=
      ht ▸ mem_zpowers t
    exact (mem_centralizer_iff.mp hafixed t htmem).symm

/-- The actual terminal involution centralizer splits over its two-core with
the prescribed five-subgroup. Every element of the complement centralizes
the fixed subgroup in the second core. -/
public theorem LargeTerminalContext.ree_complement
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    ∃ j : FiveFour.Group →* centralizer ({z} : Set G),
      Function.Injective j ∧
      j.range.IsComplement' (pCore 2 (centralizer ({z} : Set G))) ∧
      zpowers ((j FiveFour.c : centralizer ({z} : Set G)) : G) = A ∧
      ∀ g, ((j g : centralizer ({z} : Set G)) : G) ∈
        centralizer (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) := by
  obtain ⟨a, ha, hsquare, hafixed⟩ :=
    ctx.exists_compatible_squaring_element hS z hz hgen A hA hAP hAN hcard hcyc hfixed
  exact ctx.ree_complement_of_compatible_squaring_element hS z hz hgen
    A hA hAP hAN hcard hcyc hfixed a ha hsquare hafixed

end Stellmacher.Recognition
