module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.NaturalDualPoint
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.BinaryKernel
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.PerfectImage
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# Exclusion of every original natural--dual cover

The remaining ten-dimensional orbit has full actor SL5(2). The original
point join has two-group action kernel, so the original L/O2(L) action
descends through the containing Sylow overgroup. Its faithful automorphism
image is radical-free, hence perfect by the actual flag diagonal quotients.
Thus the point action is inner, contrary to the two independent original
fixed vectors and the one-dimensional containing Sylow fixed-space bound.

This closes the natural--dual branch with its original fixed kernel and all
preparation premises discharged. Positive natural covers, general quiet
preparation, the retained four-natural row and ConstrainedExclusionAt remain
with qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith 10.2.9, printed p.752. No later generation bound
or survivor theorem is used.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- A binary containing actor makes the kernel on the whole point join a two-group. -/
theorem Context.join_action_kernel_two_of_binary_actor (c : Context D t v I)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)) :
    letI := c.reduced.normal
    IsPGroup 2 (actionMk (internalModule D v I)).ker := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let P := (pointSylow T v).subgroupOf H
  let := c.reduced.normal
  let q := actionMk (internalModule D v I)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  apply q.kernel_isPGroup_of_normal_supplement K P
    ((T.isPGroup'.to_le inf_le_left).comap_subtype)
  · rw [←subgroupOf_sup (show I ≤ H from le_sup_left)
      (show pointSylow T v ≤ H from le_sup_right),subgroupOf_self]
  · have he : (q.comp K.subtype).ker = (q.subgroupMap K).ker := by
      ext x
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [he,c.action_kernel_eq_twoCore_of_binary_actor hd e]
    exact pCore_isPGroup

/-- The remaining whole binary-five containing action induces only inner
automorphisms on the original three-dimensional quotient. -/
theorem Context.pointQuotientAction_inner_of_naturalDual_cover
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∀ p : pointSylow T v,
      c.pointQuotientAction e p ∈ MulAut.innerSubgroup BinaryLinearThree.Group := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf H).map (actionMk U)
  obtain ⟨⟨E⟩,hA,_,_⟩ := c.ten_dimensional_orbit_of_naturalDual_cover e r
  let F : ActionQuotient U ≃* BinaryLinear.OuterCyclic.LinearGroup 5 :=
    (topEquiv.symm.trans ((MulEquiv.subgroupCongr hA.symm).trans E)).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 5)
  let q := actionMk U
  let f := F.toMonoidHom.comp q
  have hf : Function.Surjective f := F.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ F.injective]
    exact c.join_action_kernel_two_of_binary_actor (Or.inr rfl) E
  obtain ⟨S,hS⟩ := c.join_sylow
  have hS' : (S : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le le_sup_right]
  let B := L ⊔ pointSylow T v
  have hBH : B ≤ H := sup_le (c.escaping.strict.le.trans le_sup_left) le_sup_right
  let K := B.subgroupOf H
  let k : K ≃* B := subgroupOfEquivOfLe hBH
  let b := pCoreJoinAction 2 c.escaping.sylow_normalizes
  let a : K →* MulAut BinaryLinearThree.Group :=
    (MulAut.congr e).toMonoidHom.comp (b.comp k.toMonoidHom)
  have hi : MulAut.innerSubgroup BinaryLinearThree.Group ≤ a.range := by
    rw [←MulAut.map_innerSubgroup_congr e]
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨z,hz⟩ := inner_le_pCoreJoinAction_range 2 c.escaping.sylow_normalizes hx
    refine ⟨k.symm z,?_⟩
    change MulAut.congr e (b (k (k.symm z))) = MulAut.congr e x
    rw [k.apply_symm_apply,hz]
  have ha : pCore 2 K ≤ a.ker := by
    intro x hx
    have hk : k x ∈ pCore 2 B := by
      rw [←pCore_map_iso 2 k]
      exact mem_map_of_mem k.toMonoidHom hx
    have hb : b (k x) = 1 :=
      pCore_le_pCoreJoinAction_kernel 2 c.escaping.sylow_normalizes hk
    change MulAut.congr e (b (k x)) = 1
    rw [hb,map_one]
  have hSK : (S : Subgroup H) ≤ K := by
    rw [hS']
    exact comap_mono le_sup_right
  let := D.quasisimple
  let : Group.IsPerfect BinaryLinearThree.Group :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (L ⧸ pCore 2 L) := Selection.ModuleChoice.component_quotient_simple
    D (fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem))
  let : IsSimpleGroup BinaryLinearThree.Group := e.symm.isSimpleGroup
  let : Group.IsNilpotent (MulAut.Outer BinaryLinearThree.Group) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.isNilpotent
  have hh := BinaryLinear.sylow_overgroup_quotient_action_inner
    Matrix.PSL3Two.center_eq_bot f hf S K hSK a hi
    (hfk.comap_subtype) ha
  intro p
  exact hh ⟨k.symm (inclusion le_sup_right p),rfl⟩

/-- No original natural--dual cover survives in the constrained point context. -/
theorem Context.no_naturalDual_cover
    (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (r : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False :=
  c.no_naturalDual_cover_of_pointQuotientAction_inner e r
    (c.pointQuotientAction_inner_of_naturalDual_cover e r)
end CFSG.Quasithin.Chapter10.PointControl.Constrained
