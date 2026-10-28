module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Action
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# The literal quotient of the reselected local group

Normality of I in IT identifies I/O₂(I) with its actual image in IT/O₂(IT).
A symplectic marking makes that image centerless. Its centralizer embeds in
the two-group quotient by I; normality and the trivial two-core then kill it.
This supplies a faithful normal extension for the common-plane calculation.

Source: Aschbacher--Smith, 11.4.1(2), printed p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U) {F : BinaryField}

/-- The actual quotient IT/O₂(IT). -/
@[expose] def joinQuotient :=
  (I ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)

instance : Group (joinQuotient (I := I) (T := T)) :=
  inferInstanceAs (Group ((I ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 _))

instance : Finite (joinQuotient (I := I) (T := T)) :=
  inferInstanceAs (Finite ((I ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 _))

/-- The literal core quotient map. -/
@[expose] def joinProjection : (I ⊔ (T : Subgroup G) : Subgroup G) →*
    joinQuotient (I := I) (T := T) := QuotientGroup.mk' _

/-- The embedded image of I in IT/O₂(IT). -/
@[expose] def quotientComponent : Subgroup (joinQuotient (I := I) (T := T)) :=
  (I.subgroupOf (I ⊔ (T : Subgroup G))).map joinProjection

include D in
omit [Finite G] in
theorem joinComponent_normal : (I.subgroupOf (I ⊔ (T : Subgroup G))).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer D.sylow_normalizes_component)

include D in
omit [Finite G] in
theorem quotientComponent_normal : (quotientComponent (I := I) (T := T)).Normal := by
  let := joinComponent_normal D
  exact Normal.map inferInstance joinProjection (QuotientGroup.mk'_surjective _)

/-- Transport the marked intrinsic quotient to its actual ambient image. -/
@[expose] def quotientComponentEquiv
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))) :
    Sp F.Carrier ≃* quotientComponent (I := I) (T := T) := by
  let := joinComponent_normal D
  let e := (subgroupOfEquivOfLe (show I ≤ I ⊔ (T : Subgroup G) from le_sup_left)).symm
  exact m.groupEquiv.symm.trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      (coreQuotientEquivImage 2 (I.subgroupOf (I ⊔ (T : Subgroup G)))))

/-- The identification retains the original quotient representatives. -/
theorem quotientComponentEquiv_mk
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))) (i : I) :
    (quotientComponentEquiv D m (m.groupEquiv (QuotientGroup.mk' (pCore 2 I) i))).val =
      joinProjection (inclusion le_sup_left i) := by
  let := joinComponent_normal D
  unfold quotientComponentEquiv
  dsimp only [MulEquiv.trans_apply]
  rw [m.groupEquiv.symm_apply_apply]
  change ((coreQuotientEquivImage 2 (I.subgroupOf (I ⊔ (T : Subgroup G))))
    (QuotientGroup.mk' _ ⟨inclusion le_sup_left i, i.property⟩)).val = _
  exact coreQuotientEquivImage_apply_mk _ _ _

omit [Finite G] in
theorem quotientComponent_sup_sylow :
    quotientComponent (I := I) (T := T) ⊔
      ((T : Subgroup G).subgroupOf (I ⊔ (T : Subgroup G))).map joinProjection = ⊤ := by
  change (I.subgroupOf (I ⊔ (T : Subgroup G))).map joinProjection ⊔ _ = ⊤
  rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  exact map_top_of_surjective joinProjection (QuotientGroup.mk'_surjective _)

/-- The symplectic image is self-centralizing in the literal core quotient. -/
theorem quotientComponent_centralizer
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))) :
    centralizer (quotientComponent (I := I) (T := T) :
      Set (joinQuotient (I := I) (T := T))) = ⊥ := by
  let J := I ⊔ (T : Subgroup G)
  let H := joinQuotient (I := I) (T := T)
  let N := quotientComponent (I := I) (T := T)
  let e := quotientComponentEquiv D m
  let := quotientComponent_normal D
  have hZ : center N = ⊥ := by
    apply bot_unique
    intro n hn
    have hz : e.symm n ∈ center (Sp F.Carrier) := by
      apply mem_center_iff.mpr
      intro s
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using (mem_center_iff.mp hn (e s))
    have he : e.symm n = 1 := by simpa only [EvenProjective.center_eq_bot, mem_bot] using hz
    exact e.symm.injective (he.trans (map_one e.symm).symm)
  have hgen := quotientComponent_sup_sylow (I := I) (T := T)
  have hquot : IsPGroup 2 (H ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    (((T : Subgroup G).subgroupOf J).map joinProjection)
    (T.isPGroup'.comap_subtype.map joinProjection) hgen
  let C := centralizer (N : Set H)
  let q : C →* H ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hi : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hxN : x.val ∈ N := (QuotientGroup.eq_one_iff x.val).mp hx
    have hxZ : (⟨x.val, hxN⟩ : N) ∈ center N := by
      apply mem_center_iff.mpr
      intro n
      exact Subtype.ext (x.property n.val n.property)
    have hx1 : (⟨x.val, hxN⟩ : N) = 1 := by simpa only [hZ, mem_bot] using hxZ
    change x = 1
    exact Subtype.ext (congrArg (fun n : N => n.val) hx1)
  have hc : C ≤ pCore 2 H := le_sSup ⟨inferInstance, hquot.of_injective q hi⟩
  exact bot_unique (hc.trans (pCore_quotient_pCore_eq_bot 2).le)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
