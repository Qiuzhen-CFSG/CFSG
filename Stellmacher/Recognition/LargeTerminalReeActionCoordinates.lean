module

public import Stellmacher.Recognition.LargeTerminalReeCoreTable
public import Stellmacher.Recognition.LargeTerminalReeNormalizerLift
public import Theory.SpecificGroups.ReeTwo.CoreFiveActionNormalization
public import Theory.SpecificGroups.ReeTwo.FixingActionCensus

/-!
# Normalized actual terminal core actions

The actual ten-root table gives a marked isomorphism of the second core with
Shinoda's core. Normalize the five-action while retaining the cyclic fixed
root and its square. The compatible squaring lift then belongs to the explicit
twenty-element census of root-fixing actions. This retains its actual order
and conjugation relations; selecting the standard action remains a separate
geometric obligation.

Source: Thompson VI, pp.629–630; Shinoda (1975), pp.81–83. The five-action
normalization argument is adapted from the private calculation in
`LargeTerminalReeNonsplitExclusion`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- The actual core table yields marked coordinates, preserving the entire
cyclic fixed subgroup. -/
public theorem LargeTerminalContext.exists_ree_core_coordinates_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ e : twoCoreIn ctx.second ≃* ReeTwo.Core,
      (e.symm (ReeTwo.Core.root 9) : G) = z ∧
      zpowers (e.symm (ReeTwo.Core.root 2) : G) =
        twoCoreIn ctx.second ⊓ centralizer (A : Set G) := by
  obtain ⟨x, hx, hxz, hxt⟩ := ctx.exists_ree_core_roots_at_generator_of_cyclic
    hS A hA hAP hAN hcard hcyc hfixed z hz hgen
  let Q := twoCoreIn ctx.second
  let f : ReeTwo.Core →* Q := ReeTwo.Core.lift hx
  have hf (i : ReeTwo.CoreRoot) : f (ReeTwo.Core.root i) = x i :=
    ReeTwo.Core.lift_root hx i
  have hinj : Function.Injective f := ReeTwo.Core.hom_injective_of_last_root f (by
    rw [hf]
    intro he
    have hz1 : z = 1 := hxz.symm.trans (congrArg Subtype.val he)
    rw [hz1, orderOf_one] at hz
    contradiction)
  have hQcard : Nat.card Q = 1024 := by
    change Nat.card (twoCoreIn ctx.second) = 1024
    rw [← (ctx.involution_centralizer_core_eq_at_generator hS z hgen).1]
    exact (card_map_of_injective (centralizer ({z} : Set G)).subtype_injective).trans
      (ctx.involution_centralizer_core_eq_at_generator hS z hgen).2
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hinj, ReeTwo.Core.card.trans hQcard.symm⟩)
  exact ⟨e.symm, (congrArg Subtype.val (hf 9)).trans hxz, by
    change zpowers (f (ReeTwo.Core.root 2) : G) = _
    rw [hf, hxt]⟩

/-- Normalize an actual five-subgroup action without losing either marking. -/
public theorem LargeTerminalContext.ree_normalized_five_action
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t z : twoCoreIn ctx.second)
    (hgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (het : eQ t = ReeTwo.Core.root 2) (hez : eQ z = ReeTwo.Core.root 9) :
    ∃ (e : twoCoreIn ctx.second ≃* ReeTwo.Core) (a : A),
      e t = ReeTwo.Core.root 2 ∧ e z = ReeTwo.Core.root 9 ∧
      ctx.reeCoreAction e (inclusion hAP a) = ReeTwo.Core.c := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  let f := ctx.reeCoreAction eQ
  let rho := f (inclusion hAP a)
  have hrho : orderOf rho = 5 := by
    apply orderOf_eq_prime
    · change f (inclusion hAP a) ^ 5 = 1
      rw [← map_pow, ← map_pow]
      have hp : a ^ 5 = 1 := hA ▸ pow_card_eq_one' (x := a)
      rw [hp, map_one, map_one]
    · intro he
      have htriv : ∀ b : A, f (inclusion hAP b) = 1 := by
        intro b
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (ha b)
        rw [← hn, map_zpow, map_zpow]
        change rho ^ n = 1
        rw [he, one_zpow]
      have htop : (centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second) = ⊤ := by
        apply eq_top_iff.mpr
        intro q _
        apply mem_centralizer_iff.mpr
        intro b hb
        have hh := ctx.reeCoreAction_apply eQ (inclusion hAP ⟨b, hb⟩) q
        rw [htriv] at hh
        simp only [MulAut.one_apply, eQ.symm_apply_apply] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh.symm
      rw [htop, card_top, Nat.card_congr eQ.toEquiv, ReeTwo.Core.card] at hcard
      norm_num at hcard
  have htfix : rho (ReeTwo.Core.root 2) = ReeTwo.Core.root 2 := by
    rw [← het]
    apply eQ.symm.injective
    apply Subtype.ext
    rw [ctx.reeCoreAction_apply, eQ.symm_apply_apply]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp (hgen.le (mem_zpowers (t : G))).2 a a.property)
  obtain ⟨d, hdt, hdz, hd⟩ := ReeTwo.Core.exists_marked_conjugator_of_orderOf_eq_five rho hrho htfix
  refine ⟨eQ.trans d, a, ?_, ?_, ?_⟩
  · exact (congrArg d het).trans hdt
  · exact (congrArg d hez).trans hdz
  · change d * rho * d⁻¹ = ReeTwo.Core.c
    exact hd

/-- Actual five- and four-elements with normalized five-action. The remaining
four-action is exactly one of the twenty checked census entries. -/
public theorem LargeTerminalContext.exists_ree_census_action_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ (e : twoCoreIn ctx.second ≃* ReeTwo.Core) (c a : ctx.second) (i : Fin 20),
      (e.symm (ReeTwo.Core.root 9) : G) = z ∧
      zpowers (e.symm (ReeTwo.Core.root 2) : G) =
        twoCoreIn ctx.second ⊓ centralizer (A : Set G) ∧
      zpowers (c : G) = A ∧ c ^ 5 = 1 ∧ a ^ 4 = 1 ∧
      a * c * a⁻¹ = c ^ 2 ∧
      ctx.reeCoreAction e c = ReeTwo.Core.c ∧
      ctx.reeCoreAction e a = ReeTwo.Core.FixingActionCensus.representative i := by
  obtain ⟨eQ, hez, het⟩ := ctx.exists_ree_core_coordinates_of_cyclic
    hS A hA hAP hAN hcard hcyc hfixed z hz hgen
  let t := eQ.symm (ReeTwo.Core.root 2)
  let zQ := eQ.symm (ReeTwo.Core.root 9)
  obtain ⟨e, cA, het', hez', hc⟩ := ctx.ree_normalized_five_action
    A hA hAP hcard t zQ het eQ (eQ.apply_symm_apply _) (eQ.apply_symm_apply _)
  have hezG : (e.symm (ReeTwo.Core.root 9) : G) = z := by
    rw [← hez', e.symm_apply_apply]
    exact hez
  have hetG : zpowers (e.symm (ReeTwo.Core.root 2) : G) =
      twoCoreIn ctx.second ⊓ centralizer (A : Set G) := by
    rw [← het', e.symm_apply_apply]
    exact het
  obtain ⟨aC, ha, hsquare, hafixed⟩ := ctx.exists_compatible_squaring_element
    hS z hz hgen A hA hAP hAN hcard hcyc hfixed
  have hCP := ctx.involution_centralizer_eq_second hS z hz hgen
  let a : ctx.second := ⟨aC, hCP ▸ aC.property⟩
  let c : ctx.second := inclusion hAP cA
  let f := ctx.reeCoreAction e
  change f c = ReeTwo.Core.c at hc
  have hc5 : c ^ 5 = 1 := by
    change inclusion hAP cA ^ 5 = 1
    rw [← map_pow, show cA ^ 5 = 1 from hA ▸ pow_card_eq_one' (x := cA), map_one]
  have ha4 : a ^ 4 = 1 := Subtype.ext (congrArg (fun q : centralizer ({z} : Set G) => (q : G))
    (show aC ^ 4 = 1 from ha ▸ pow_orderOf_eq_one aC))
  have hac : a * c * a⁻¹ = c ^ 2 := Subtype.ext (hsquare cA cA.property)
  have hconj : f a * ReeTwo.Core.c * (f a)⁻¹ = ReeTwo.Core.c ^ 2 := by
    rw [← hc]
    rw [← map_inv, ← map_mul, ← map_mul, hac, map_pow]
  have hfix : f a (ReeTwo.Core.root 2) = ReeTwo.Core.root 2 := by
    rw [← het']
    apply e.symm.injective
    apply Subtype.ext
    rw [ctx.reeCoreAction_apply, e.symm_apply_apply]
    have htF := het.le (mem_zpowers (t : G))
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hafixed t htF).symm
  obtain ⟨i, hi⟩ := ReeTwo.Core.FixingActionCensus.exhaustive_of_conj_c_root_two
    (f a) hconj hfix
  have hcA : zpowers (c : G) = A := by
    have hne : c ≠ 1 := by
      intro h
      have hh : ReeTwo.Core.c = 1 := hc.symm.trans (by rw [h, map_one])
      have ho := ReeTwo.Core.orderOf_c
      rw [hh, orderOf_one] at ho
      exact (by decide : (1 : ℕ) ≠ 5) ho
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    have horder : orderOf (c : G) = 5 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hc5 hne
    exact eq_of_le_of_card_ge (zpowers_le.mpr cA.property)
      (by rw [Nat.card_zpowers, horder, hA])
  exact ⟨e, c, a, i, hezG, hetG, hcA, hc5, ha4, hac, hc, hi⟩

end Stellmacher.Recognition
