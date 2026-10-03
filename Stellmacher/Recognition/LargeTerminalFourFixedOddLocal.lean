module

public import Stellmacher.Recognition.LargeTerminalFiveNormalizer
public import Stellmacher.Recognition.LargeTerminalFourFixedOddExclusion

/-!
# Odd-local exclusions in the noncyclic four-fixed alternative

The actual five-normalizer is confined to the second local group. This
promotes the specified order-five subgroup to an ambient Sylow subgroup and
forces its normalizer to centralize the distinguished involution. The coprime
core-action argument excludes fifteen from the centralizer order of every
five-fixed involution outside the residual. Sylow centralizer nonfusion also
excludes conjugacy with the distinguished involution.

The confinement hypothesis of the intermediate results is discharged here.
The two-local solvability and characteristic-two assumptions are supplied by
`LargeTerminalContext`; no odd-local solvability assumption is used.

Source: Thompson VI, printed p.630, the final four-group contradiction.
-/

namespace Stellmacher.Recognition

open SectionsFiveToSeven Subgroup

universe u

/-- In the actual noncyclic four-fixed alternative, the specified five-subgroup
is Sylow, its normalizer centralizes the distinguished involution, and the
outside fixed involutions have centralizer order indivisible by fifteen. -/
public theorem LargeTerminalContext.noncyclic_four_fixed_odd_local_data
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    (∃ P : Sylow 5 G, (P : Subgroup G) = A) ∧
      normalizer (A : Set G) ≤ centralizer ({z} : Set G) ∧
      ∀ y : G, y ∈ twoCoreIn ctx.second → y ∈ centralizer (A : Set G) →
        y ∉ ctx.firstResidual → orderOf y = 2 →
        ¬ 15 ∣ Nat.card (centralizer ({y} : Set G)) := by
  have hN := ctx.five_normalizer_le_second hS A hA hAP hAN hcard hncyc hfixed
  refine ⟨ctx.exists_sylow_five_of_normalizer_le_second hS A hA hN,
    hN.trans (ctx.second_le_residual_normalizer.trans
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen)), ?_⟩
  intro y _ hyA _ hy2
  exact ctx.not_fifteen_dvd_fixed_involution_centralizer_of_core_action
    hS A hA hN hcard y hyA hy2

/-- The two direct exclusions needed by the final four-group contradiction,
with all normalizer-confinement and Sylow premises discharged. -/
public theorem LargeTerminalContext.noncyclic_four_fixed_involution_exclusions
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (y : G) (hyQ : y ∈ twoCoreIn ctx.second)
    (hyA : y ∈ centralizer (A : Set G)) (hyR : y ∉ ctx.firstResidual)
    (hy2 : orderOf y = 2) :
    (¬ IsConj z y) ∧ ¬ 15 ∣ Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨⟨P, hP⟩, hN, h15⟩ :=
    ctx.noncyclic_four_fixed_odd_local_data hS A hA hAP hAN hcard hncyc hfixed z hz hgen
  have hNP : normalizer (P : Set G) ≤ centralizer ({z} : Set G) := by
    change normalizer ((P : Subgroup G) : Set G) ≤ _
    rwa [hP]
  have hyP : y ∈ centralizer (P : Set G) := by
    change y ∈ centralizer ((P : Subgroup G) : Set G)
    rwa [hP]
  exact ⟨ctx.not_isConj_of_five_sylow_normalizer P z hgen hNP y hyP hyR,
    h15 y hyQ hyA hyR hy2⟩

end Stellmacher.Recognition
