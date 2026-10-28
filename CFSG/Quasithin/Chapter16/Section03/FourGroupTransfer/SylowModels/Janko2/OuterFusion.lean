module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.Fusion
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Outer
public import GorensteinWalter.PSL2InvolutionFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# Central-class fusion in outer J₂ fixed-subgroup components

The checked Sylow element `sElement 3` is fixed by the chosen outer involution
and squares to `FirstFusion.t`. Outer-involution conjugacy transports this
square root to every outer fixed subgroup. Sylow conjugacy and the whole-center
identity show that every automorphism preserves the conjugacy class of `t`.

The sole earlier-source premise identifies the fixed subgroup with Aut(PSL₃(2)).
Each actual component is PSL₃(2) and has index two, so the transported square
belongs to it. The exceptional PSL₂(7) isomorphism and involution conjugacy
then fuse every component involution to the central class of the actual J₂
carrier. No additional center, placement, or fusion premise is retained.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178 / PDF p.1195,
using precisely the outer clause of 16.1.5(8), printed p.1172. The concrete
checks use the retained ATLAS J2G1-p100B0 carrier and unchanged Seed enumeration.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open PairNormalizer PairNormalizer.SylowData SecondParabolic
open OtherPreliminaries.JankoTwoHigmanSims
open scoped Pointwise

private theorem central_class_characteristic (e : MulAut Carrier) :
    IsConj FirstFusion.t (e FirstFusion.t) := by
  classical
  let S := sylow FirstParabolic.card_l₁
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier S R
  have hm : Seed.s.map (MulAut.conj g).toMonoidHom = Seed.s.map e.toMonoidHom :=
    congrArg Sylow.toSubgroup hg
  have hc := congrArg (fun U : Subgroup Carrier => (center U).map U.subtype) hm
  rw [map_center_image_of_injective _ _ (MulAut.conj g).injective,
    map_center_image_of_injective _ _ e.injective,
    ← map_map, ← map_map, center_s, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers] at hc
  change zpowers ((MulAut.conj g) FirstFusion.t) = zpowers (e FirstFusion.t) at hc
  have hm : e FirstFusion.t ∈ zpowers ((MulAut.conj g) FirstFusion.t) := by
    rw [hc]
    exact mem_zpowers _
  have ho : orderOf ((MulAut.conj g) FirstFusion.t) = 2 :=
    ((MulAut.conj g).orderOf_eq _).trans central_involution_order
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hm
  have hh : e FirstFusion.t = 1 ∨ e FirstFusion.t = (MulAut.conj g) FirstFusion.t := by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hi2 := Finset.mem_range.mp hi
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  rcases hh with h | h
  · exact (FirstFusion.t_ne_one (e.map_eq_one_iff.mp h)).elim
  · exact isConj_iff.mpr ⟨g, h.symm⟩

set_option maxRecDepth 100000 in
private theorem outer_fixed_square :
    extensionAction Seed.outerElement (sElement 3) = sElement 3 ∧
      sElement 3 ^ 2 = FirstFusion.t := by
  constructor
  · apply Sporadic.LeechRelated.J2.inclusion_injective
    change extension.subtype Seed.outerElement * inclusion (sElement 3) *
      (extension.subtype Seed.outerElement)⁻¹ = inclusion (sElement 3)
    rw [outerElement_inclusion, sElement_inclusion]
    decide +kernel
  · apply Sporadic.LeechRelated.J2.inclusion_injective
    rw [map_pow, sElement_inclusion, FirstFusion.inclusion_t]
    decide +kernel

private theorem outer_action_order : orderOf (extensionAction Seed.outerElement) = 2 := by
  rw [orderOf_injective extensionAction extensionAction_injective]
  exact orderOf_eq_prime outerElement_sq (fun h =>
    outerElement_not_mem_range (h ▸ intoExtension.range.one_mem))

private theorem outer_action_not_inner :
    ¬ ∃ g : Carrier, extensionAction Seed.outerElement = MulAut.conj g := by
  rintro ⟨g, hg⟩
  exact outerElement_not_mem_range ⟨g, extensionAction_injective (by
    rw [extensionAction_inner, hg])⟩

private theorem exists_fixed_central_square (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) :
    ∃ w : r.fixedSubgroup, IsConj FirstFusion.t ((w : Carrier) ^ 2) := by
  have h := (J2Outer.outer_involution_fusion _ outer_action_order outer_action_not_inner).symm.trans
    (J2Outer.outer_involution_fusion r hr ho)
  obtain ⟨e, he⟩ := isConj_iff.mp h
  have hr' : r = MulAut.congr e (extensionAction Seed.outerElement) := he.symm
  subst r
  let w : (MulAut.congr e (extensionAction Seed.outerElement)).fixedSubgroup :=
    ⟨e (sElement 3), by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change e (extensionAction Seed.outerElement (e.symm (e (sElement 3)))) = e (sElement 3)
      rw [e.symm_apply_apply, outer_fixed_square.1]⟩
  refine ⟨w, ?_⟩
  change IsConj FirstFusion.t ((e (sElement 3)) ^ 2)
  rw [← map_pow, outer_fixed_square.2]
  exact central_class_characteristic e

private theorem involutions_conjugate_of_psl2_equiv
    {H : Type*} [Group H] (e : H ≃* GorensteinWalter.PSL2 (ZMod 7))
    (x y : H) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hinv {z : GorensteinWalter.PSL2 (ZMod 7)} (hz : orderOf z = 2) :
      GorensteinWalter.IsInvolution z := by
    refine ⟨?_, ?_⟩
    · intro he
      simp [he] at hz
    · simpa only [hz] using pow_orderOf_eq_one z
  have hseven : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) := by
    refine ⟨7, 1, by decide, by decide, by decide, ?_⟩
    norm_num
  obtain ⟨u, hu⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power
    (ZMod 7) hseven (e x) (e y) (hinv ((e.orderOf_eq x).trans hx))
      (hinv ((e.orderOf_eq y).trans hy))
  have hc : IsConj (e x) (e y) := isConj_iff.mpr ⟨u, hu⟩
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using
    e.symm.toMonoidHom.map_isConj hc

private theorem psl3_involutions_conjugate
    (x y : Matrix.PSL3Two.PSL) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  involutions_conjugate_of_psl2_equiv
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm x y hx hy

private theorem component_involutions_conjugate (r : MulAut Carrier)
    (model : Nonempty (r.fixedSubgroup ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))))
    (D : Subgroup r.fixedSubgroup) (hD : IsComponent r.fixedSubgroup D)
    (x y : D) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨f⟩ := model
  obtain ⟨g⟩ := Matrix.PSL3Two.Automorphisms.component_equiv _ (hD.map_equiv f)
  let e : D ≃* Matrix.PSL3Two.PSL := (f.subgroupMap D).trans g
  have hc := psl3_involutions_conjugate (e x) (e y)
    ((e.orderOf_eq x).trans hx) ((e.orderOf_eq y).trans hy)
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using
    e.symm.toMonoidHom.map_isConj hc

/-- Central-class fusion for every actual component of an outer fixed subgroup.
The sole earlier-source input is the exact outer clause of 16.1.5(8). -/
theorem j2_outer_component_involution_fusion (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g)
    (model : Nonempty (r.fixedSubgroup ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))) :
    J2ComponentInvolutionFusion r := by
  intro D hD x hx
  obtain ⟨w, hw⟩ := exists_fixed_central_square r hr ho
  have hindex : D.index = 2 := by
    obtain ⟨f⟩ := model
    obtain ⟨g⟩ := Matrix.PSL3Two.Automorphisms.component_equiv _ (hD.map_equiv f)
    have hcD : Nat.card D = 168 :=
      (Nat.card_congr ((f.subgroupMap D).trans g).toEquiv).trans Matrix.PSL3Two.card_PSL
    have hcF : Nat.card r.fixedSubgroup = 336 :=
      (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut
    have hi := D.card_mul_index
    rw [hcD, hcF] at hi
    omega
  let y : D := ⟨w ^ 2, D.sq_mem_of_index_two hindex w⟩
  have hy : orderOf y = 2 := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hw
    have he : (MulAut.conj a) FirstFusion.t = (w : Carrier) ^ 2 := ha
    have hh : orderOf ((w : Carrier) ^ 2) = 2 := by
      rw [← he, (MulAut.conj a).orderOf_eq]
      exact central_involution_order
    exact (orderOf_coe y).symm.trans
      ((orderOf_coe (y : r.fixedSubgroup)).symm.trans hh)
  have hc := component_involutions_conjugate r model D hD y x hy hx
  exact hw.trans (r.fixedSubgroup.subtype.map_isConj (D.subtype.map_isConj hc))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
