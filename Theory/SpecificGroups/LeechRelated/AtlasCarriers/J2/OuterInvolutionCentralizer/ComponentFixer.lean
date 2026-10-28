module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.FixedComponents
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
/-!
# The commuting pointwise fixer of the J2 outer component

The actual outer fixed group is Aut(PSL3(2)), whose component has trivial centralizer. Thus the commuting pointwise fixer embeds in Out(J2). The concrete involution extension makes that outer group have order at most two. Source: Aschbacher–Smith 2.5.19, printed p.561.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics GeneratorPair

theorem outer_card_le_two : Nat.card (MulAut.Outer Carrier) ≤ 2 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup Carrier)
  let f := q.comp extensionAction
  have hs : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    extensionAction_surjective
  let N := generated.subgroupOf extension
  have hgen : N ⊔ zpowers extensionInvolution = ⊤ := by
    apply (map_injective extension.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show generated ≤ extension from le_sup_left),
      MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hN : N.map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    change q (extensionAction x) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨⟨x, hx⟩, (extensionAction_inner ⟨x, hx⟩).symm⟩
  have himg := congrArg (map f) hgen
  rw [Subgroup.map_sup, hN, bot_sup_eq, map_top_of_surjective f hs] at himg
  have hc := Nat.le_of_dvd (Nat.card_pos (α := zpowers extensionInvolution))
    (Subgroup.card_map_dvd (zpowers extensionInvolution) f)
  rw [himg, Nat.card_congr (topEquiv : (⊤ : Subgroup (MulAut.Outer Carrier)) ≃* _).toEquiv,
    Nat.card_zpowers] at hc
  exact hc.trans (orderOf_le_of_pow_eq_one (by decide : 0 < 2) (by
    apply Subtype.ext
    change involution ^ 2 = 1
    simpa only [pow_two] using involution_mul_self))

namespace OuterInvolutionCentralizer

theorem fixed_component_centralizer_eq_bot (a : MulAut Carrier)
    (e : a.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    centralizer (B : Set a.fixedSubgroup) = ⊥ := by
  have he := component_map_eq_inner a e B hB
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  rw [map_one]
  apply mem_bot.mp
  apply (MulAut.centralizer_innerSubgroup_eq_bot
    Matrix.PSL3Two.Automorphisms.center_psl_eq_bot).le
  intro y hy
  rw [← he] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  change e w * e x = e x * e w
  simpa only [map_mul] using congrArg e (hx w hw)

theorem commuting_component_fixer_card_le_two
    (a : MulAut Carrier) (ha : orderOf a = 2)
    (ho : a ∉ (MulAut.conj : Carrier →* MulAut Carrier).range)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    Nat.card (centralizer ({a} : Set (MulAut Carrier)) ⊓
      fixingSubgroup (MulAut Carrier) (B.map a.fixedSubgroup.subtype : Set Carrier) :
        Subgroup (MulAut Carrier)) ≤ 2 := by
  obtain ⟨e⟩ := outer_fixed_equiv a ha ho
  let C : Subgroup (MulAut Carrier) := centralizer ({a} : Set (MulAut Carrier)) ⊓
    fixingSubgroup (MulAut Carrier) (B.map a.fixedSubgroup.subtype : Set Carrier)
  let f : C →* MulAut.Outer Carrier :=
    (QuotientGroup.mk' (MulAut.innerSubgroup Carrier)).comp C.subtype
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro b hb
    have hbinner : (b : MulAut Carrier) ∈ MulAut.innerSubgroup Carrier :=
      (QuotientGroup.eq_one_iff _).mp hb
    obtain ⟨x, hx⟩ := hbinner
    have hci : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
      intro x y h
      have h' : intoExtension x = intoExtension y := extensionAction_injective (by
        simpa only [extensionAction_inner] using h)
      exact (Subgroup.inclusion_injective (show generated ≤ extension from le_sup_left)) h'
    have hcomm : MulAut.conj x * a = a * MulAut.conj x := by
      rw [hx]
      exact mem_centralizer_singleton_iff.mp b.property.1
    have hfixed : a x = x := by
      apply hci
      have hconj : MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
        ext z
        simp
      rw [hconj, ← hcomm, mul_inv_cancel_right]
    let y : a.fixedSubgroup := ⟨x, (MulAut.mem_fixedSubgroup a x).mpr hfixed⟩
    have hy : y ∈ centralizer (B : Set a.fixedSubgroup) := by
      intro w hw
      apply Subtype.ext
      have hwfix := b.property.2 ⟨(w : Carrier), mem_map_of_mem a.fixedSubgroup.subtype hw⟩
      change (b : MulAut Carrier) (w : Carrier) = (w : Carrier) at hwfix
      rw [← hx] at hwfix
      exact (mul_inv_eq_iff_eq_mul.mp hwfix).symm
    have hyone : y = 1 := mem_bot.mp ((fixed_component_centralizer_eq_bot a e B hB).le hy)
    have hxone : x = 1 := congrArg Subtype.val hyone
    apply mem_bot.mpr
    apply Subtype.ext
    change (b : MulAut Carrier) = 1
    rw [← hx, hxone, map_one]
  exact (Nat.card_le_card_of_injective f hi).trans outer_card_le_two
end OuterInvolutionCentralizer
end Sporadic.LeechRelated.J2
