module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.MarkedFixedLift
import all Theory.SpecificGroups.AlternatingSix.M10.OuterInvolutions.Fixed
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.TwoClasses

/-!
# The fixed D10 supplies a source non-core witness

The diagonal involution fixes D10 in the actual A6. Lift this subgroup
through the proved fixed-normalizer isomorphism. Its involutions lie in the
original C_G(B), hence in the z-class, and two have product of order five.
They cannot both lie in the centralizer two-core. H-control of s-fusion
then transports this witness to exclude z from O2(C_G(s)).

This supplies exactly the non-core consequence used in J.2.9 without requiring
the stronger unused identification of the whole order-forty centralizer.

Source: Aschbacher–Smith J.2.9, printed p.438 (PDF p.449).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

noncomputable def fixedInnerMap (β : AlternatingSix.ShadowLocal.AutA6) :
    GLS3.Chapter5.automorphismFixedSubgroup β→*
      centralizer ({β}:Set AlternatingSix.ShadowLocal.AutA6) where
  toFun x := ⟨MulAut.conj (x:AlternatingSix.ShadowLocal.A6),mem_centralizer_singleton_iff.mpr
    ((AlternatingSix.M10.OuterInvolutions.commute_inner_iff β x).mpr x.property).symm.eq⟩
  map_one' := Subtype.ext (map_one MulAut.conj)
  map_mul' x y := Subtype.ext (map_mul MulAut.conj (x:AlternatingSix.ShadowLocal.A6) y)

lemma fixedInnerMap_injective (β : AlternatingSix.ShadowLocal.AutA6) :
    Function.Injective (fixedInnerMap β) := by
  intro x y h
  apply Subtype.ext
  exact AlternatingSix.ShadowLocal.inner_injective (congrArg Subtype.val h)

lemma dihedral_five_pair : ∃ x y : DihedralGroup 5,
    orderOf x=2 ∧ orderOf y=2 ∧ orderOf (x*y)=5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨.sr 0,.sr 1,?_,?_,?_⟩ <;> apply orderOf_eq_prime <;> decide +kernel

public theorem diagonal_z_pair_source
    (e : c.NormalizerQuotient≃*AlternatingSix.ShadowLocal.AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom=AlternatingSix.M10.extension)
    (u : c.NB) (hu : c.InvertsB (u:G)) (hu2 : orderOf u=2)
    (hn : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural) :
    ∃x y : centralizer ({(u:G)}:Set G),
      orderOf x=2 ∧ orderOf y=2 ∧ orderOf (x*y)=5 ∧ IsConj c.z (x:G) ∧ IsConj c.z (y:G) := by
  let β := e (c.normalizerQuotientMap u)
  obtain ⟨b⟩ := AlternatingSix.ShadowLocal.outside_natural_involution_fixed_equiv_dihedral
    β (c.inverter_marked_order e u hu hu2) hn
  let a := c.markedFixedEquiv e u hu
  let f := (fixedInnerMap β).comp b.symm.toMonoidHom
  let F := (c.fixedAmbientMap u).comp (a.symm.toMonoidHom.comp f)
  have hF : Function.Injective F := (c.fixedAmbientMap_injective u).comp
    (a.symm.injective.comp ((fixedInnerMap_injective β).comp b.symm.injective))
  have hGB (x : DihedralGroup 5) : (F x:G)∈c.GB := by
    have hmodel : (f x:AlternatingSix.ShadowLocal.AutA6)∈AlternatingSix.M10.extension :=
      AlternatingSix.M10.Action.inner_le_extension ⟨b.symm x,rfl⟩
    have ha : (a (a.symm (f x)):AlternatingSix.ShadowLocal.AutA6)∈AlternatingSix.M10.extension := by
      rw [a.apply_symm_apply];exact hmodel
    rw [c.markedFixedEquiv_apply,←hM] at ha
    obtain ⟨y,hy,he⟩ := ha
    have he' : y=c.normalizerQuotientMap (a.symm (f x)) := e.injective he
    have hh : (a.symm (f x):c.NB)∈c.centralizerImage.comap c.normalizerQuotientMap := by
      change c.normalizerQuotientMap (a.symm (f x))∈c.centralizerImage
      rw [←he'];exact hy
    rw [c.centralizerImage_comap (SourceCompletion.B_card c)] at hh
    change (c.fixedAmbientMap u (a.symm (f x)) : G)∈c.GB
    rw [c.fixedAmbientMap_apply]
    exact hh
  have hconj (x : DihedralGroup 5) (hx : orderOf x=2) : IsConj c.z (F x:G) := by
    have ho : orderOf (F x:G)=2 := (Subgroup.orderOf_coe (F x)).trans
      ((orderOf_injective F hF x).trans hx)
    exact (SourceCompletion.cubic_involutions c (F x) (hGB x) ho).symm
  obtain ⟨x,y,hx,hy,hxy⟩ := dihedral_five_pair
  exact ⟨F x,F y,(orderOf_injective F hF x).trans hx,(orderOf_injective F hF y).trans hy,
    by rw [←map_mul,orderOf_injective F hF,hxy],hconj x hx,hconj y hy⟩

public theorem z_not_mem_twoCore_source : c.z∉c.Gs.pCoreIn 2 := by
  obtain ⟨e,hM⟩ := c.normalizer_equiv_autA6_source
  obtain ⟨k,hk,hui,hu2⟩ := SourceCompletion.exists_inverter c
  let u : c.NB := ⟨k*c.s*k⁻¹,c.mem_NB_of_inverts hui⟩
  have hsu : IsConj c.s (u:G) := isConj_iff.mpr ⟨k,rfl⟩
  have huN : orderOf u=2 := (Subgroup.orderOf_coe u).symm.trans hu2
  have hun : e (c.normalizerQuotientMap u)∉AlternatingSix.ShadowLocal.natural := by
    intro h
    exact c.not_isConj_z_s_source
      (hsu.trans (c.natural_inverter_z_fused_source e hM u hui huN h)).symm
  obtain ⟨x,y,hx,hy,hxy,hzx,hzy⟩ := c.diagonal_z_pair_source e hM u hui huN hun
  let C := centralizer ({(u:G)}:Set G)
  have hn : (x:G)∉C.pCoreIn 2 ∨ (y:G)∉C.pCoreIn 2 := by
    by_contra h
    push Not at h
    have hm : (x:G)*(y:G)∈C.pCoreIn 2 := (C.pCoreIn 2).mul_mem h.1 h.2
    have ho : orderOf (⟨(x:G)*(y:G),hm⟩:C.pCoreIn 2)=5 := by
      rw [←Subgroup.orderOf_coe]
      exact (Subgroup.orderOf_coe (x*y)).trans hxy
    have hne : (⟨(x:G)*(y:G),hm⟩:C.pCoreIn 2)≠1 := by
      intro he;simp [he] at ho
    have hd := (isPGroup_pCoreIn 2 C).dvd_orderOf hne
    rw [ho] at hd
    norm_num at hd
  rcases hn with hn | hn
  · exact c.z_not_mem_twoCore_of_local_witness c.H_eq_centralizer_z.symm
      c.H_s_fusion_source hsu x.property hzx hn
  · exact c.z_not_mem_twoCore_of_local_witness c.H_eq_centralizer_z.symm
      c.H_s_fusion_source hsu y.property hzy hn

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
