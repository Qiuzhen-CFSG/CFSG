module

public import Stellmacher.Recognition.LargeTerminalFiveFixedFour
public import Theory.GroupTheory.SylowCentralizerNonfusion

/-!
# The four-group alternative for the actual five-fixed subgroup

The fixed subgroup in the second local core has order four. If it is not
cyclic, it has exponent two and contains an involution outside the first
residual: otherwise its four elements would inject into the residual center
of order two. This provides the actual ambient involution for the remaining
fusion and odd-local arguments, without replacing the fixed subgroup by an
abstract group of the same order.

Source: Thompson VI, printed pp.629--630, the four-group contradiction.
The involution-fusion and odd-local exclusion needed to finish cyclicity
are separate from the elementary reduction proved here.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- In the noncyclic case there is an actual five-fixed involution outside
of the first residual. No ambient Sylow-five assertion is needed here. -/
public theorem LargeTerminalContext.exists_five_fixed_involution_of_not_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second))) :
    ∃ y : G, y ∈ twoCoreIn ctx.second ∧ y ∈ centralizer (A : Set G) ∧
      y ∉ ctx.firstResidual ∧ orderOf y = 2 := by
  let Q := twoCoreIn ctx.second
  let F := (centralizer (A : Set G)).subgroupOf Q
  have hnot : ¬ ∀ y : F, (y : G) ∈ ctx.firstResidual := by
    intro hle
    let f : F → center ctx.firstResidual := fun y =>
      ⟨⟨y, hle y⟩, hfixed y.property⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : center ctx.firstResidual => ((z : ctx.firstResidual) : G)) h))
    have hbound := Nat.card_le_card_of_injective f hf
    rw [ctx.first_residual_structure.2.2.2.1] at hbound
    change Nat.card F = 4 at hcard
    omega
  obtain ⟨y, hyR⟩ := not_forall.mp hnot
  have hexp : Monoid.exponent F = 2 :=
    (not_isCyclic_iff_exponent_eq_prime Nat.prime_two hcard).mp hncyc
  have hpow : y ^ 2 = 1 := by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one _
  have hyPow : (y : G) ^ 2 = 1 :=
    congrArg (fun t : F => ((t : Q) : G)) hpow
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨y, y.val.property, y.property, hyR,
    orderOf_eq_prime hyPow (fun h => hyR (h ▸ ctx.firstResidual.one_mem))⟩

/-- Once the actual five-subgroup is Sylow and its normalizer centralizes
the omega-central involution, no fixed element outside the residual fuses to it. -/
public theorem LargeTerminalContext.not_isConj_of_five_sylow_normalizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (P : Sylow 5 G) (z : G)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (hN : normalizer (P : Set G) ≤ centralizer ({z} : Set G))
    (y : G) (hy : y ∈ centralizer (P : Set G)) (hyR : y ∉ ctx.firstResidual) :
    ¬ IsConj z y := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hzR : z ∈ ctx.firstResidual := by
    have hle : zpowers z ≤ ctx.firstResidual := by
      rw [hgen, ← ctx.first_residual_center_eq_omegaOneCenter]
      exact map_subtype_le _
    exact hle (mem_zpowers z)
  have hz : z ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hN ((P : Subgroup G).le_normalizer ha))
  intro hconj
  exact hyR ((P.eq_of_isConj_of_normalizer_le_centralizer z y hz hy hN hconj).symm ▸ hzR)

end Stellmacher.Recognition
