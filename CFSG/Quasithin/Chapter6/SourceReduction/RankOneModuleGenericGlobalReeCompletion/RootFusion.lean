module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Fusion
public import Theory.SpecificGroups.ReeF4.SourceCompletion.RootClasses
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.LongCentralizer

/-!
# Converse fusion for the two native Ree root classes

The literal right normalizer map sends the original residual-center involutions
into the native long-root class. Native conjugacy within each root class,
together with the already proved extension-to-ambient fusion, transports the
original long/short nonfusion to arbitrary full-endpoint representatives.
Consequently ambient fusion is equivalent to extension fusion for elements
whose native representatives lie in either root class. The same statement
uses the entire original common-normalizer map, hence applies to its Sylow.

The two root-class membership hypotheses are explicit: exhaustion of all
native involutions remains necessary to remove them. No ambient short
centralizer containment, order comparison or recognition is assumed here.
Source: Aschbacher–Smith F.4.27(3), F.4.30 and F.4.35, printed pp.288,290–292
(`refs/quasithin.pdf`), with the actual prepared pair of 5.3.1–3, pp.658–659.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G]
variable [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp
/-- The literal right marking sends every original residual-center involution to the native long-root class. -/
theorem Preparation.ree_long_root_marking
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (z : center (residual H)) (hz2 : orderOf z = 2) :
    let zN : normalizer (residual H : Set G) :=
      ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
    ∃ t : Model m, IsLongRootInvolution t ∧
      D.rightToCarrier zN = D.extension.baseHom t := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  let a : P := ⟨z.val.val,hKP z.val.property⟩
  let zN : normalizer (residual H : Set G) :=
    ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
  have hm := d.ree_parameter_positive h hp m 1 .suzuki D.pure.right
  let f := (ReeF4.Parabolics.parabolic m .suzuki).subtype.comp D.pure.right.toMonoidHom
  have hres : (residual H).subgroupOf P = solvableResidual P := by
    have hr : (solvableResidual P).map P.subtype = residual H :=
      d.parabolic_residuals h hH.1.1.2 hp 1
    rw [←hr]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have hR : ((residual H).subgroupOf P).map f =
      ReeF4.Parabolics.localFactor m .suzuki := by
    rw [hres,show f = (ReeF4.Parabolics.parabolic m .suzuki).subtype.comp
      D.pure.right.toMonoidHom from rfl,←map_map,
      map_solvableResidual_eq _ D.pure.right.surjective]
    exact ReeF4.Parabolics.parabolic_solvableResidual_map hm .suzuki
  have haZ := center_image hKP f hR z
  rw [ReeF4.SourceCompletion.suzuki_center_eq_longRoot hm] at haZ
  have hf : Function.Injective f :=
    (ReeF4.Parabolics.parabolic m .suzuki).subtype_injective.comp D.pure.right.injective
  have hzG : orderOf z.val.val = 2 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hz2]
  have ha1 : f a ≠ 1 := by
    intro hh
    have hz1 : z.val.val = 1 := congrArg Subtype.val (hf (hh.trans (map_one f).symm))
    simp [hz1] at hzG
  have hmark : D.rightToCarrier zN = D.extension.baseHom (f a) := by
    apply Subtype.ext
    exact D.right_marking a
  obtain ⟨r,hr⟩ := (mem_longRootGroup m _).mp haZ
  refine ⟨f a,⟨r,?_,?_⟩,hmark⟩
  · intro hr0
    apply ha1
    rw [←hr, hr0, longRootElement_zero]
  · exact hr ▸ IsConj.refl (longRootElement m r)

include he
/-- Full endpoint elements in different native root classes cannot fuse in the original ambient group. -/
theorem Preparation.ree_root_endpoint_nonfusion
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    {i j : Bool} (x : D.extension.family i) (y : D.extension.family j)
    {tx ty : Model m} (hx : IsLongRootInvolution tx) (hy : IsShortRootInvolution ty)
    (hxm : D.extension.baseHom tx = x.val) (hym : D.extension.baseHom ty = y.val) :
    ¬ IsConj (D.endpointInverse i x) (D.endpointInverse j y) := by
  obtain ⟨z,hz,hz2,_⟩ := d.ree_right_center_involution h hH hp m he
  obtain ⟨z0,hz0,rfl⟩ := hz
  let zc : center (residual H) := ⟨z0,hz0⟩
  have hzc : orderOf zc = 2 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
    exact hz2
  let zN : normalizer (residual H : Set G) :=
    ⟨z0.val,(residual H).le_normalizer z0.property⟩
  obtain ⟨tz,htz,hmz⟩ := d.ree_long_root_marking h hH hp m D zc hzc
  obtain ⟨tv,v,htv,_,_,hv2,hmv,_,_,_,hnf⟩ :=
    d.ree_short_centralizer_comparison h hH hp m he D
  let ze : D.extension.family true := ⟨D.rightToCarrier zN,(D.full.right zN).property⟩
  let ve : D.extension.family false := ⟨D.leftToCarrier v,(D.full.left v).property⟩
  have hzE : orderOf ze.val = 2 := by
    rw [orderOf_injective D.rightToCarrier D.rightToCarrier_injective,←Subgroup.orderOf_coe]
    exact hz2
  have hvE : orderOf ve.val = 2 := by
    rw [orderOf_injective D.leftToCarrier D.leftToCarrier_injective,←Subgroup.orderOf_coe]
    exact hv2
  have hzx : IsConj ze.val x.val := by
    change IsConj (D.rightToCarrier zN) x.val
    rw [hmz,←hxm]
    exact D.extension.baseHom.map_isConj (ReeF4.SourceCompletion.long_class_isConj htz hx)
  have hvy : IsConj ve.val y.val := by
    change IsConj (D.leftToCarrier v) y.val
    rw [hmv,←hym]
    exact D.extension.baseHom.map_isConj (ReeF4.SourceCompletion.short_class_isConj htv hy)
  have hzxG := d.ree_extension_involution_fusion h hp m D ze x hzE hzx
  have hvyG := d.ree_extension_involution_fusion h hp m D ve y hvE hvy
  rw [D.endpointInverse_right] at hzxG
  rw [D.endpointInverse_left] at hvyG
  intro hxy
  exact hnf z0.val (mem_map_of_mem _ hz0) hz2 (hzxG.trans (hxy.trans hvyG.symm))

/-- Converse fusion on the union of the two actual native root classes, through the same full endpoint maps. Native exhaustion is not asserted here. -/
theorem Preparation.ree_root_endpoint_fusion_iff
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    {i j : Bool} (x : D.extension.family i) (y : D.extension.family j)
    {tx ty : Model m}
    (hx : IsLongRootInvolution tx ∨ IsShortRootInvolution tx)
    (hy : IsLongRootInvolution ty ∨ IsShortRootInvolution ty)
    (hxm : D.extension.baseHom tx = x.val) (hym : D.extension.baseHom ty = y.val) :
    IsConj (D.endpointInverse i x) (D.endpointInverse j y) ↔ IsConj x.val y.val := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  have hi : Function.Injective D.extension.baseHom :=
    (MonoidHom.injective_codRestrict _ _ _).mpr (ReeF4.SmallCompletion.conj_injective m hm)
  have hx2 : orderOf x.val = 2 := by
    rw [←hxm,orderOf_injective D.extension.baseHom hi]
    exact hx.elim orderOf_of_isLongRootInvolution orderOf_of_isShortRootInvolution
  refine ⟨?_,fun hc => d.ree_extension_involution_fusion h hp m D x y hx2 hc⟩
  intro hc
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rw [←hxm,←hym]
    exact D.extension.baseHom.map_isConj (ReeF4.SourceCompletion.long_class_isConj hx hy)
  · exact (d.ree_root_endpoint_nonfusion h hH hp m he D x y hx hy hxm hym hc).elim
  · exact (d.ree_root_endpoint_nonfusion h hH hp m he D y x hy hx hym hxm hc.symm).elim
  · rw [←hxm,←hym]
    exact D.extension.baseHom.map_isConj (ReeF4.SourceCompletion.short_class_isConj hx hy)

/-- The same equivalence on the entire original common normalizer, in particular on its original Sylow, whenever the native representatives lie in the two root classes. -/
theorem Preparation.ree_root_middle_fusion_iff
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (x y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    {tx ty : Model m}
    (hx : IsLongRootInvolution tx ∨ IsShortRootInvolution tx)
    (hy : IsLongRootInvolution ty ∨ IsShortRootInvolution ty)
    (hxm : D.extension.baseHom tx = D.middleToCarrier x)
    (hym : D.extension.baseHom ty = D.middleToCarrier y) :
    IsConj x.val y.val ↔ IsConj (D.middleToCarrier x) (D.middleToCarrier y) := by
  let xL := inclusion (show normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
    normalizer (L : Set G) from inf_le_left) x
  let yL := inclusion (show normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
    normalizer (L : Set G) from inf_le_left) y
  have hxm' : D.extension.baseHom tx = D.leftToCarrier xL := by
    rw [D.middleToCarrier_left] at hxm
    exact hxm
  have hym' : D.extension.baseHom ty = D.leftToCarrier yL := by
    rw [D.middleToCarrier_left] at hym
    exact hym
  have hh := d.ree_root_endpoint_fusion_iff h hH hp m he D
    (i := false) (j := false)
    ⟨D.leftToCarrier xL,(D.full.left xL).property⟩
    ⟨D.leftToCarrier yL,(D.full.left yL).property⟩ hx hy hxm' hym'
  rw [D.endpointInverse_left,D.endpointInverse_left] at hh
  change IsConj xL.val yL.val ↔ IsConj (D.leftToCarrier xL) (D.leftToCarrier yL) at hh
  have hxv : xL.val = x.val := Subgroup.coe_inclusion _ x
  have hyv : yL.val = y.val := Subgroup.coe_inclusion _ y
  rw [hxv,hyv,←hxm',←hym',hxm,hym] at hh
  exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
