module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceActionRows
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.BinaryLinear.SylowImage

/-!
# Natural binary overcomponents of the original H-star residual

Transport the actual chosen natural action from Y to YT, retaining its
literal quotient by O₂(Y). This action fills the binary linear group, so
the original Sylow subgroup maps onto a full linear Sylow. The H-star image
is solvable in every positive binary dimension by the flag calculation. The
kernel on X lies in O₂(Y); hence X would be solvable, contradicting its
quasisimple two-core quotient.

This argument covers proper overcomponents as well as equality. Its original
guarded applications remove all three natural binary rows from the
source residual construction. The other proper embeddings and final 12.2.7,
12.2.18--20 assembly remain with qt-d-12213-hstar-natural.

Source: Aschbacher--Smith, 12.2.7, printed pp.797--798, comparing A.3.12
and E.2.2 with the actual modules of 12.2.2. Imported concrete model proofs
retain their ATLAS attribution and LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ} {Y W : Subgroup G}

private def naturalCoordinates (E : ChosenModule T Y W)
    (e : ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) :
    letI := E.elementary; Additive W ≃ₗ[ZMod 2] Space n := by
  let := E.elementary
  exact ((MulEquiv.toAdditiveRight E.spaceEquiv).toLinearEquiv
    (ZMod.map_smul _)).symm.trans e.linearEquiv

private def naturalJoinMap (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (e : ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) :
    (Y ⊔ (T : Subgroup G) : Subgroup G) →* LinearGroup n := by
  let := E.elementary
  exact (BinaryLinear.SmallParabolicLevi.linearGroupCongr (naturalCoordinates E e)).toMonoidHom.comp
    (chosenJoinLinearAction E hT)

private theorem naturalJoinMap_component (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (e : ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) (y : Y) :
    naturalJoinMap E hT e ⟨y,(show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left) y.property⟩ =
      slEquivLinear n (e.groupEquiv (QuotientGroup.mk' (pCore 2 Y) y)) := by
  let := E.elementary
  let c := naturalCoordinates E e
  apply LinearEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  change c ((chosenJoinLinearAction E hT ⟨y,(show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left) y.property⟩)
    (c.symm (e.linearEquiv w))) = _
  have hc (z : E.space) : c.symm (e.linearEquiv z) =
      Additive.ofMul (E.spaceEquiv (Multiplicative.ofAdd z)) := by
    simp [c,naturalCoordinates]
  have ha : (chosenJoinLinearAction E hT ⟨y,(show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left) y.property⟩)
      (c.symm (e.linearEquiv w)) = c.symm (e.linearEquiv (E.chosenAction y w)) := by
    rw [hc,hc]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (y : G) * (E.spaceEquiv (Multiplicative.ofAdd w) : G) * (y : G)⁻¹ =
      (E.spaceEquiv (Multiplicative.ofAdd (E.chosenAction y w)) : G)
    rw [E.spaceEquiv_apply,E.spaceEquiv_apply]
    rfl
  rw [ha,c.apply_symm_apply]
  exact e.intertwines (QuotientGroup.mk' (pCore 2 Y) y) w

private theorem naturalJoinMap_surjective (E : ChosenModule T Y W)
    (hT : (T : Subgroup G) ≤ normalizer (W : Set G))
    (e : ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) :
    Function.Surjective (naturalJoinMap E hT e) := by
  intro g
  obtain ⟨q,hq⟩ := e.groupEquiv.surjective ((slEquivLinear n).symm g)
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Y) q
  refine ⟨⟨y,(show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left) y.property⟩,?_⟩
  rw [naturalJoinMap_component,hq,MulEquiv.apply_symm_apply]
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  {L V H X Y W : Subgroup G}

/-- Every positive-dimensional natural binary overcomponent is impossible. -/
theorem HStarGeneratingComponent.not_natural_overcomponent_at
    (C : HStarGeneratingComponent T L H X) (hn : 0 < n)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    ¬ Nonempty (ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) := by
  rintro ⟨e⟩
  let J := Y ⊔ (T : Subgroup G)
  have hHJ : H ≤ J := by rw [← C.generates]; exact sup_le_sup_right hXY _
  let hT := ((structural Y hY).2.2 W E).1
  let a := naturalJoinMap E hT e
  let j := inclusion hHJ
  let f := a.comp j
  let R := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let S := R.mapSurjective (naturalJoinMap_surjective E hT e)
  have hS : ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H).map f =
      (S : Subgroup (LinearGroup n)) := by
    change ((T : Subgroup G).subgroupOf H).map (a.comp j) =
      ((T : Subgroup G).subgroupOf J).map a
    rw [← Subgroup.map_map]
    congr 1
    apply map_injective J.subtype_injective
    rw [Subgroup.map_map]
    change ((T : Subgroup G).subgroupOf H).map H.subtype = _
    rw [map_subgroupOf_eq_of_le hH.1.1.2,map_subgroupOf_eq_of_le le_sup_right]
  let := ChapterB.minimalParabolic_image_solvable_binary hn (T.subtype hH.1.1.2)
    (chosen_hstar_minimalParabolic_at h D structural hTI hH) f S hS
  let b : X →* f.range := f.rangeRestrict.comp (inclusion C.component.1)
  let q : X →* (Y ⧸ pCore 2 Y) := (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hXY)
  have hk : b.ker ≤ q.ker := by
    intro x hx
    have hx' : a ⟨(x : G),hHJ (C.component.1 x.property)⟩ = 1 :=
      congrArg Subtype.val (show b x = 1 from hx)
    have he := naturalJoinMap_component E hT e ((inclusion hXY) x)
    have he' : slEquivLinear n (e.groupEquiv (q x)) = 1 := he.symm.trans hx'
    apply e.groupEquiv.injective
    apply (slEquivLinear n).injective
    simpa only [map_one] using he'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let k : q.ker →* pCore 2 Y :=
    ((inclusion hXY).comp q.ker.subtype).codRestrict _ (by
      intro x
      exact (QuotientGroup.eq_one_iff _).mp x.property)
  have hi : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 Y => ((z : Y) : G)) he
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective hi
  let : Group.IsSolvable b.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hk) (inclusion_injective hk)
  let : Group.IsSolvable X := Group.isSolvable_of_ker_le_range b.ker.subtype b (by simp)
  let := C.quasisimple
  let : IsSimpleGroup ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) := IsQuasisimple.simple
  let : Nontrivial (X ⧸ pCore 2 X) :=
    (QuotientGroup.mk'_surjective (center (X ⧸ pCore 2 X))).nontrivial
  exact Group.IsPerfect.not_isSolvable (X ⧸ pCore 2 X) inferInstance
/-- The recovered three-or-five interface, retained without changing its statement. -/
theorem HStarGeneratingComponent.not_natural_three_or_five_overcomponent_at
    (C : HStarGeneratingComponent T L H X) (hn : n = 3 ∨ n = 5)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    ¬ Nonempty (ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) :=
  C.not_natural_overcomponent_at (by omega) h D structural hTI hH hXY hY E

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original guarded residual construction excludes the natural three-
and five-dimensional rows on every chosen module of its actual overcomponent.
The remaining proper embeddings stay with qt-d-12213-hstar-natural. -/
theorem chosen_hstar_residual_overcomponent_natural_restrictions_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X ≤ Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      ∀ (W : Subgroup G) (E : ChosenModule T Y W) (n : ℕ), n = 3 ∨ n = 5 →
        ¬ Nonempty (ActionEquiv E.quotientAction (specialLinearNatural (k := ZMod 2) n)) := by
  obtain ⟨X,Y,C,hres,hXY,hY⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  exact ⟨X,Y,C,hres,hXY,hY,fun _ E _ hn =>
    C.not_natural_three_or_five_overcomponent_at hn h D structural hTI hH hXY hY E⟩
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
