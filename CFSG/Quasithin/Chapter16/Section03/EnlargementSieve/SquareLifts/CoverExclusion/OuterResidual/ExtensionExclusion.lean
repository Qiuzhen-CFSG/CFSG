module

public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Excluding the elementary-kernel HS outer row

The inherited component is A₆ or A₈ and has trivial center. Its map into
the full quotient fixed subgroup is therefore injective. An extension
with kernel E₁₆ and quotient S₅ has order 1920, divisible by neither
|A₆| nor |A₈|. This excludes that row without assuming anything about
the action on the normal kernel.

Source: Aschbacher–Smith, 16.1.5(10), 16.3.9(4), and the outer branch
of 16.3.11(3), printed pp.1172, 1180–1181.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion.OuterResidual
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem centerless_of_alternating {H : Type*} [Group H] {n : ℕ}
    (e : H ≃* alternatingGroup (Fin n)) (hn : 4 ≤ n) : center H = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply e.injective
  have hx' := ((centerCongr e) ⟨x, hx⟩).property
  change e x ∈ center (alternatingGroup (Fin n)) at hx'
  rw [alternatingGroup.center_eq_bot (by simpa using hn)] at hx'
  simpa using hx'

private theorem central_quotient_injective {K : Type*} [Group K]
    (H : Subgroup K) (hc : center H = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp H.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxZ : (x : K) ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hxC : x ∈ center H := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hxZ y)
  rwa [hc] at hxC

private theorem elementaryExtension_card {C : Type*} [Group C] [Finite C]
    (h : IsHSElementaryExtension C) : Nat.card C = 1920 := by
  obtain ⟨Q, hQn, ⟨eQ⟩, ⟨eR⟩⟩ := h
  let := hQn
  have hq : Nat.card Q = 16 := by
    rw [Nat.card_congr eQ.toEquiv]
    norm_num [E16, C2, Nat.card_eq_fintype_card]
  have hr : Q.index = 120 := by
    rw [Subgroup.index_eq_card, Nat.card_congr eR.toEquiv]
    norm_num [S5, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [← Q.card_mul_index, hq, hr]

/-- The actual A₆ or A₈ fixed component excludes the E₁₆-by-S₅ row. -/
theorem not_elementaryExtension_of_alternating {K M : Type*}
    [Group K] [Finite K] [Group M] [Finite M]
    (a : MulAut K) (e : K ⧸ center K ≃* M) (H : Subgroup K)
    (hf : H ≤ a.fixedSubgroup)
    (hm : Nonempty (H ≃* A6) ∨ Nonempty (H ≃* A8)) :
    ¬ IsHSElementaryExtension (MulAut.centralQuotientAction e a).fixedSubgroup := by
  intro hext
  have hcent : center H = ⊥ := by
    rcases hm with hm | hm
    · obtain ⟨d⟩ := hm
      exact centerless_of_alternating d (by decide)
    · obtain ⟨d⟩ := hm
      exact centerless_of_alternating d (by decide)
  let f : H →* (MulAut.centralQuotientAction e a).fixedSubgroup := {
    toFun x := ⟨e (QuotientGroup.mk' (center K) x), by
      rw [MulAut.mem_fixedSubgroup, MulAut.centralQuotientAction_apply,
        (MulAut.mem_fixedSubgroup a x).mp (hf x.property)]⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by apply Subtype.ext; simp }
  have hi : Function.Injective f := by
    intro x y heq
    apply central_quotient_injective H hcent
    exact e.injective (congrArg Subtype.val heq)
  have hd := card_dvd_of_injective f hi
  rw [elementaryExtension_card hext] at hd
  rcases hm with hm | hm
  · obtain ⟨d⟩ := hm
    rw [Nat.card_congr d.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hd
    norm_num at hd
  · obtain ⟨d⟩ := hm
    rw [Nat.card_congr d.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hd
    norm_num at hd

end CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion.OuterResidual
