module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.CoverLifts.Inputs
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Inner actors from centers of quotient fixed subgroups

A nonidentity central element of a quotient fixed subgroup centralizes the
image of the perfect component. Lifting the element through the central
quotient then centralizes the component itself: homomorphisms from a perfect
group that agree modulo a central kernel are equal. The full action-image
hypothesis makes its conjugation an actual inner actor.

For a four-group of actors, the C₂ factor in the outer M₁₂ row therefore
proves the inner-index bound without assuming an outer-automorphism bound.
Source: Aschbacher–Smith 16.1.5(4) and the last paragraph of 16.3.6,
printed pp.1171 and 1179 / PDF pp.1188 and 1196.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
variable {H A M : Type*} [Group H] [Group A] [Group M]

/-- A nontrivial center of a quotient fixed subgroup gives a nontrivial inner actor. -/
theorem innerActors_ne_bot_of_fixed_center
    (J : Subgroup H) [Group.IsPerfect J]
    (α : A →* MulAut H)
    (himage : α.range = centralizer (J.map MulAut.conj : Set (MulAut H)))
    (e : H ⧸ center H ≃* M) (a : A)
    (hfix : ∀ j : J, α a j = j)
    (z : (MulAut.centralQuotientAction e (α a)).fixedSubgroup)
    (hz : z ∈ center (MulAut.centralQuotientAction e (α a)).fixedSubgroup)
    (hne : z ≠ 1) : innerActors α ≠ ⊥ := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center H))
  obtain ⟨f, hf⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center H))) (z : M)
  change q f = (z : M) at hf
  have hfJ : f ∈ centralizer (J : Set H) := by
    have heq : (MulAut.conj f).toMonoidHom.comp J.subtype = J.subtype := by
      apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
        (QuotientGroup.mk' (center H)) (by rw [QuotientGroup.ker_mk'])
      apply MonoidHom.ext
      intro j
      apply e.injective
      have hj : q j ∈ (MulAut.centralQuotientAction e (α a)).fixedSubgroup := by
        rw [MulAut.mem_fixedSubgroup]
        change MulAut.centralQuotientAction e (α a) (e (QuotientGroup.mk' (center H) j)) = _
        rw [MulAut.centralQuotientAction_apply, hfix]
        rfl
      have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨q j, hj⟩)
      change q j * (z : M) = (z : M) * q j at hc
      change q (f * (j : H) * f⁻¹) = q j
      rw [map_mul, map_mul, map_inv, hf, ← hc]
      group
    intro j hj
    have hj' := DFunLike.congr_fun heq ⟨j, hj⟩
    change f * j * f⁻¹ = j at hj'
    exact ((mul_inv_eq_iff_eq_mul).mp hj').symm
  have hr : MulAut.conj f ∈ α.range := by
    rw [himage]
    exact (conj_mem_centralizer_iff J f).mpr hfJ
  obtain ⟨b, hb⟩ := hr
  have hbin : b ∈ innerActors α := ⟨f, hb.symm⟩
  intro hbot
  have hb1 : b = 1 := by simpa only [hbot, mem_bot] using hbin
  have hconj : MulAut.conj f = 1 := by rw [← hb, hb1, map_one]
  have hfZ : f ∈ center H := by rw [← conj_kernel]; exact hconj
  apply hne
  apply Subtype.ext
  change (z : M) = 1
  rw [← hf]
  change e (QuotientGroup.mk' (center H) f) = 1
  rw [(show QuotientGroup.mk' (center H) f = 1 from (QuotientGroup.eq_one_iff f).mpr hfZ), map_one]

/-- The central C₂ factor in a fixed subgroup forces index at most two in four actors. -/
theorem innerActors_index_le_two_of_fixed_product [Finite A]
    (J : Subgroup H) [Group.IsPerfect J]
    (α : A →* MulAut H)
    (himage : α.range = centralizer (J.map MulAut.conj : Set (MulAut H)))
    (hcard : Nat.card A = 4)
    (e : H ⧸ center H ≃* M) (a : A)
    (hfix : ∀ j : J, α a j = j)
    {B : Type*} [Group B]
    (f : (MulAut.centralQuotientAction e (α a)).fixedSubgroup ≃*
      Multiplicative (ZMod 2) × B) : (innerActors α).index ≤ 2 := by
  let c : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  let z := f.symm (c, 1)
  have hz : z ∈ center (MulAut.centralQuotientAction e (α a)).fixedSubgroup := by
    apply mem_center_iff.mpr
    intro x
    apply f.injective
    simp only [map_mul, z, f.apply_symm_apply]
    apply Prod.ext
    · exact mul_comm _ _
    · simp
  have hne : z ≠ 1 := by
    intro hh
    have hh' := congrArg (fun x => (f x).1) hh
    norm_num [z, c] at hh'
  have hn := innerActors_ne_bot_of_fixed_center J α himage e a hfix z hz hne
  have hl := (innerActors α).one_lt_card_iff_ne_bot.mpr hn
  have hm := (innerActors α).card_mul_index
  rw [hcard] at hm
  nlinarith
end CFSG.Quasithin.Chapter16.FourGroupTransfer.CoverLifts.TableReduction
