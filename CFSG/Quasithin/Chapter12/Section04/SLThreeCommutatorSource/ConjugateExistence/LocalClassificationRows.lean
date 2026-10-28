module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperEight
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperLinear
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperRows
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperExterior

/-!
# The 12.2.7 overcomponent sieve with intrinsic minimal parabolicity

These source variants use the actual minimal-parabolic H instead of
unavailable global TI and no-escape assumptions. The natural, exterior and
A₈ rows are excluded through the original quotient actions and the binary
flag calculation. A proper overcomponent therefore has literal O₂,Z
quotient A₇, with the original four- or six-dimensional chosen modules.

The internal imports share the existing coordinate and quotient transports
with the earlier 12.2.7 proof family; no private declaration enters a public
type and no shared module's API is changed.
Source: Aschbacher–Smith, 12.2.7, printed pp.797–798.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource ChapterI.Section06To08
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  {L H X Y W : Subgroup G}

theorem HStarGeneratingComponent.not_natural_overcomponent_of_parabolic
    (C : HStarGeneratingComponent T L H X) (hn : 0 < n)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
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
    hP f S hS
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

theorem HStarGeneratingComponent.proper_rows_of_parabolic
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) : HStarProperRows E := by
  let := E.actionCentralizer_normal
  have hn := C.not_solvableSylowOvergroups_of_proper_at structural modules hH hXY hY
  have hthree (e : (Y ⧸ pCore 2 Y) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      False := hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv e
        (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two (by simp))))
  cases modules Y W hY E with
  | linear n degree action =>
    exact (C.not_natural_overcomponent_of_parabolic (by omega) structural hH hP hXY.le hY E
      ⟨action⟩).elim
  | linearThreeExtension groupEquiv _ _ => exact (hthree groupEquiv).elim
  | linearFiveExterior groupEquiv dimension irreducible =>
    exact .exterior groupEquiv dimension irreducible
  | alternating n lower upper action =>
    by_cases hs : n = 5 ∨ n = 6
    · exact (hn (solvableSylow_of_faithful_small hY E n hs action.groupEquiv)).elim
    · exact .alternating n (by omega) action
  | alternatingSevenFour groupEquiv dimension => exact .sevenFour groupEquiv dimension
  | g2 action =>
    exact (hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv action.groupEquiv
      Atlas.G2.binaryDerived_solvableSylowOvergroups))).elim
  | tripleSix groupEquiv _ _ _ =>
    exact (hn (solvableSylow_of_core (SolvableSylowOvergroups.of_equiv groupEquiv
      solvableSylow_hexEven))).elim


theorem HStarGeneratingComponent.not_binary_join_actor_of_parabolic
    (C : HStarGeneratingComponent T L H X)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X ≤ Y) {m : ℕ}
    (a : (Y ⊔ (T : Subgroup G) : Subgroup G) →* LinearGroup (m+1))
    (hs : Function.Surjective a) (hk : IsPGroup 2 a.ker) : False := by
  let J := Y ⊔ (T : Subgroup G)
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hHJ : H ≤ J := by
    rw [← C.generates]
    exact sup_le_sup hXY le_rfl
  let B := H.subgroupOf J
  let c : B ≃* H := subgroupOfEquivOfLe hHJ
  have hUB : (U : Subgroup J) ≤ B := fun _ ht => hH.1.1.2 ht
  have hu := (hP.1).map c.symm.mapSubgroup
  have heU : ((T.subtype hH.1.1.2 : Subgroup H)).map c.symm.toMonoidHom =
      (U : Subgroup J).subgroupOf B := by
    ext x
    rw [mem_map_equiv]
    rfl
  change Order.HasUniqueMaximalOver
    ((T.subtype hH.1.1.2 : Subgroup H).map c.symm.toMonoidHom)
    ((⊤ : Subgroup H).map c.symm.toMonoidHom) at hu
  rw [heU,map_top_of_surjective _ c.symm.surjective] at hu
  let : Group.IsSolvable B :=
    BinaryLinear.SylowFlagOvergroups.solvable_of_two_kernel_uniqueMaximal a hs hk U B hUB hu
  let : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (f := c.toMonoidHom) c.surjective
  exact Chapter1.mem_L_not_isSolvable (C.exists_maximal_overcomponent hH).1
    (Group.isSolvable_of_isSolvable_injective (f := inclusion C.component.1)
      (inclusion_injective _))


theorem HStarGeneratingComponent.not_exterior_five_overcomponent_of_parabolic
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W)
    (e : (Y ⧸ pCore 2 Y) ≃* SL5TenDimensional.Group)
    (hd : Module.finrank (ZMod 2) E.space = 10)
    (hi : IsIrreducible E.quotientAction) : False := by
  let := hi
  obtain ⟨q,c,_,hc⟩ := SL5ExteriorSquare.square_coordinates_of_finrank_ten E.quotientAction e hd
  let model : ActionEquiv E.quotientAction (SL5TenDimensional.exteriorAction 2) := ⟨q,c,hc⟩
  have hTW := ((structural Y hY).2.2 W E).1
  obtain ⟨a,ha,hk⟩ := join_actor_of_self_normalizing E hTW _
    (SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0)
    SL5TenDimensional.ExteriorNormalizer.normalizer_two model
  let b := (slEquivLinear 5).toMonoidHom.comp a
  apply C.not_binary_join_actor_of_parabolic hH hP hXY b
    ((slEquivLinear 5).surjective.comp ha)
  rw [MonoidHom.ker_comp_of_injective _ _ (slEquivLinear 5).injective]
  exact hk


theorem HStarGeneratingComponent.proper_alternating_rows_of_parabolic
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal
    (∃ n, (n = 7 ∨ n = 8) ∧ Nonempty (ActionEquiv E.faithfulCentralAction
      (alternatingNatural n))) ∨
    (Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) ∧
      Module.finrank (ZMod 2) E.space = 4) := by
  let := E.actionCentralizer_normal
  cases C.proper_rows_of_parabolic structural modules hH hP hXY hY E with
  | exterior e hd hi =>
    exact (C.not_exterior_five_overcomponent_of_parabolic structural hH hP hXY.le hY E e hd hi).elim
  | alternating n hn action => exact Or.inl ⟨n,hn,⟨action⟩⟩
  | sevenFour e hd => exact Or.inr ⟨⟨e⟩,hd⟩


theorem HStarGeneratingComponent.not_eight_overcomponent_of_parabolic
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W)
    (e : letI := E.actionCentralizer_normal
      (Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 8)) : False := by
  let := E.actionCentralizer_normal
  let := hY.quasisimple
  let r := e.toMonoidHom.comp E.coreToFaithful
  have hr' : Function.Surjective r := e.surjective.comp E.coreToFaithful_surjective
  have hi : Function.Injective r := AlternatingEight.reduced_cover_injective r hr'
    (pCore_quotient_pCore_eq_bot 2)
  let cY : (Y ⧸ pCore 2 Y) ≃* LinearGroup 4 :=
    (MulEquiv.ofBijective r ⟨hi,hr'⟩).trans
      (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
        (projectiveEquivLinear (by decide : 0 < 4)))
  let J := Y ⊔ (T : Subgroup G)
  let A := Y.subgroupOf J
  let B := X.subgroupOf J
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hKJ : X ≤ J := hXY.le.trans le_sup_left
  let cC : A ≃* Y := subgroupOfEquivOfLe le_sup_left
  let cB : B ≃* X := subgroupOfEquivOfLe hKJ
  let eC : (A ⧸ pCore 2 A) ≃* LinearGroup 4 :=
    (QuotientGroup.congr _ _ cC (pCore_map_iso 2 _)).trans cY
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Y.le_normalizer E.sylow_normalizes_component)
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.maximal_faithful.1.1
  let : Group.IsPerfect X := Chapter1.mem_L_isPerfect
    (C.exists_maximal_overcomponent hH).1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := cC.symm.toMonoidHom) cC.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := cB.symm.toMonoidHom) cB.symm.surjective
  have hgen : A ⊔ (U : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left]
    change Y ⊔ ((T : Subgroup G).subgroupOf J).map J.subtype = _
    rw [map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  have hBC : B ≤ A := comap_mono hXY.le
  have hne : B ≠ A := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hKJ,map_subgroupOf_eq_of_le le_sup_left] at hh
    exact hXY.ne hh
  have hns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable
      (C.exists_maximal_overcomponent hH).1
      (Group.isSolvable_of_surjective (f := cB.toMonoidHom) cB.surjective)
  have hUB : (U : Subgroup J) ≤ normalizer (B : Set J) :=
    (comap_mono (C.normalized_of_overcomponent_at structural modules hH hXY.le hY)).trans (le_normalizer_comap J.subtype)
  obtain ⟨a,ha,hka⟩ := BinaryLinear.SylowFlagOvergroups.exists_inner_four_core_action
    A eC U hgen B hBC hne hns hUB
  exact C.not_binary_join_actor_of_parabolic hH hP hXY.le a ha hka


theorem HStarGeneratingComponent.proper_seven_rows_of_parabolic
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal
    Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃* alternatingGroup (Fin 7)) ∧
      (Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 7)) ∨
        Module.finrank (ZMod 2) E.space = 4) := by
  let := E.actionCentralizer_normal
  rcases C.proper_alternating_rows_of_parabolic structural modules hH hP hXY hY E with
    ⟨n,hn,⟨e⟩⟩ | ⟨e,hd⟩
  · rcases hn with rfl | rfl
    · exact ⟨⟨e.groupEquiv⟩,Or.inl ⟨e⟩⟩
    · exact (C.not_eight_overcomponent_of_parabolic structural modules hH hP hXY hY E e.groupEquiv).elim
  · exact ⟨e,Or.inr hd⟩


theorem HStarGeneratingComponent.proper_seven_source_of_parabolic
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (E : ChosenModule T Y W) :
    Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) ∧
      (T : Subgroup G) ≤ normalizer (W : Set G) ∧
      (Module.finrank (ZMod 2) E.space = 4 ∨ Module.finrank (ZMod 2) E.space = 6) := by
  let := E.actionCentralizer_normal
  let := hY.quasisimple
  obtain ⟨⟨e⟩,hrows⟩ := C.proper_seven_rows_of_parabolic structural modules hH hP hXY hY E
  let r := e.toMonoidHom.comp E.coreToFaithful
  have hr : Function.Surjective r := e.surjective.comp E.coreToFaithful_surjective
  have hk : r.ker = center (Y ⧸ pCore 2 Y) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 7)),MonoidHom.comap_bot] at hh
    exact hh
  let f := r.comp (QuotientGroup.mk' (pCore 2 Y))
  have hf : Function.Surjective f := hr.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = centralPreimage (pCore 2 Y) := by
    change r.ker.comap (QuotientGroup.mk' (pCore 2 Y)) = _
    rw [hk]
    rfl
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩,((structural Y hY).2.2 W E).1,?_⟩
  rcases hrows with ha | hd
  · obtain ⟨a⟩ := ha
    obtain ⟨b⟩ := E.fullAction_of_odd_alternating_quotient (by decide) (by decide) a
    right
    calc
      Module.finrank (ZMod 2) E.space =
          Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 7)) := b.linearEquiv.finrank_eq
      _ = 6 := by simpa using BinaryPermutation.finrank_natural_odd (Ω := Fin 7) (by decide)
  · exact Or.inl hd


end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
