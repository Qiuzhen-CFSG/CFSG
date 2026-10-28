module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Components of the adequate outer group

Perfect subgroups lie in the displayed product because its quotient is cyclic.
Their projection to the cubic factor is trivial, so every component lies in
the actual A₆ factor. This gives uniqueness of components. A perfect whole
actor is impossible, since it would still have a nontrivial cubic quotient.
No representation or fixed-space splitting is used.

These are the group deductions used in 13.8.16 and 15.3.49(i)–(k).
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(4),
printed p.105; pp.952 and 1143–1144.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D : Type*} [Group D]

/-- Every ordinary component is contained in the specified A₆ subgroup. -/
theorem outerSixThreeShape_component_le_first (c : ChapterB.OuterSixThreeShape D)
    {A : Subgroup D} (hA : IsComponent D A) : A ≤ c.first := by
  let := hA.2
  let P := c.first ⊔ c.second
  let : P.Normal := outerSixThreeShape_product_normal c
  let : IsCyclic (D ⧸ P) := outerSixThreeShape_quotient_isCyclic c
  let : CommGroup (D ⧸ P) := IsCyclic.commGroup
  have hAP : A ≤ P := le_of_isPerfect_of_solvable_quotient A P
  let f : A →* c.second := (MonoidHom.snd c.first c.second).comp
    (c.product.symm.toMonoidHom.comp (inclusion hAP))
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  let : Group.IsSolvable c.second := Group.isSolvable_of_isSolvable_injective
    (f := c.secondEquiv.toMonoidHom) c.secondEquiv.injective
  have hz : f.range = ⊥ := by
    by_contra hn
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro x hx
  let y := c.product.symm ⟨x, hAP hx⟩
  have hy : y.2 = 1 := mem_bot.mp (hz ▸ (show f ⟨x, hx⟩ ∈ f.range from ⟨⟨x, hx⟩, rfl⟩))
  have he := c.product_apply y.1 y.2
  have hv : (c.product y : D) = x := congrArg Subtype.val (c.product.apply_symm_apply _)
  rw [hv, hy, coe_one, mul_one] at he
  exact he ▸ y.1.property

/-- The adequate outer group has at most one ordinary component. -/
theorem outerSixThreeShape_components_eq (c : ChapterB.OuterSixThreeShape D)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) : A = B := by
  have ha := outerSixThreeShape_component_le_first c hA
  have hb := outerSixThreeShape_component_le_first c hB
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
  have ht : IsComponent c.first ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have he := ((hA.subgroupOf ha).eq_of_le ht le_top).trans
    ((hB.subgroupOf hb).eq_of_le ht le_top).symm
  have hm := congrArg (Subgroup.map c.first.subtype) he
  simpa only [map_subgroupOf_eq_of_le ha, map_subgroupOf_eq_of_le hb] using hm

/-- Perfectness excludes the outer shape, without any module assertions. -/
theorem outerSixThreeShape_not_perfect [Group.IsPerfect D]
    (c : ChapterB.OuterSixThreeShape D) : False := by
  let := outerSixThreeShape_product_normal c
  let := outerSixThreeShape_quotient_isCyclic c
  let : CommGroup (D ⧸ (c.first ⊔ c.second)) := IsCyclic.commGroup
  have ht : c.first ⊔ c.second = ⊤ := by
    apply top_unique
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  let e : D ≃* c.first × c.second :=
    topEquiv.symm.trans ((MulEquiv.subgroupCongr ht.symm).trans c.product.symm)
  let f : D →* Multiplicative (ZMod 3) :=
    c.secondEquiv.toMonoidHom.comp ((MonoidHom.snd c.first c.second).comp e.toMonoidHom)
  let : Group.IsPerfect (Multiplicative (ZMod 3)) :=
    Group.IsPerfect.ofSurjective (f := f)
      (c.secondEquiv.surjective.comp (Prod.snd_surjective.comp e.surjective))
  exact Group.IsPerfect.not_isMulCommutative (Multiplicative (ZMod 3)) inferInstance

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
