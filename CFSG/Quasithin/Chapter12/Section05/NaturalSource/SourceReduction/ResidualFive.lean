module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalClassificationOpening
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalClassificationRows
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceResidualFive
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperSeven

/-!
# The original H-star residual for the point-escape argument

The nonsolvable H-star subgroup is minimal parabolic. The earlier source
classification constructs its actual two-residual and an overcomponent.
In the equal case, the seven module rows identify the residual quotient
as A₅. In the proper A₇ case, the characteristic action on the original
join and the original Sylow supplement give the same intrinsic quotient.
All maps retain the full two-core denominator.

The internal import reuses the characteristic seven-letter action and
proper-image lemmas without widening their existing public interface.
The two local recognition proofs use the minimal-parabolic hypothesis
proved for this H, avoiding the unrelated global TI premise of the older
entry points. Noncommuting applies this residual identification to the
literal weak-closure construction; earlier structural/module discharge
belongs to qt-d-1332-source.

Source: Aschbacher--Smith, 12.2.7, 12.2.18, 12.3.2 and 12.4.1,
printed pp.797--801,807,812.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourcePointEscape
open Subgroup Theory.GroupTheory Representation
open Section02 Section02.RecognitionSource ChapterI.Section06To08
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L H X Y : Subgroup G}
private theorem proper_five_or_alternating_action
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) :
    Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) ∨
      ∃ f : H →* alternatingGroup (Fin 7), Group.IsSolvable f.ker := by
  have hTX := C.normalized_of_overcomponent_at structural modules hH hXY.le hY
  have hTY := (structural Y hY).1
  have hlocal := (C.exists_maximal_overcomponent hH).1
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
  obtain ⟨⟨e⟩,_⟩ := C.proper_seven_source_of_parabolic structural modules hH hP hXY hY E
  obtain ⟨π,a,hπ,hker,hres,hA,hs⟩ := seven_join_action hTY e
  let J := Y ⊔ (T : Subgroup G)
  have hHJ : H ≤ J := by
    rw [←C.generates]
    exact sup_le_sup hXY.le le_rfl
  let g := a.comp (inclusion hHJ)
  let := hs
  have hgker : Group.IsSolvable g.ker := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hHJ).subgroupComap a.ker) (by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : a.ker => (z.val : G)) he)))
  rcases alternatingGroup.SevenComponent.range_eq_alternating_or_top a hA with ha | ha
  · right
    let f := g.codRestrict (alternatingGroup (Fin 7)) (fun x => ha ▸ (show a (inclusion hHJ x) ∈ a.range from ⟨_,rfl⟩))
    refine ⟨f,?_⟩
    have he : f.ker = g.ker := MonoidHom.ker_codRestrict _ _ _
    exact he.symm ▸ hgker
  left
  have has : Function.Surjective a := a.range_eq_top.mp ha
  let U := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).mapSurjective has
  let B := X.subgroupOf Y
  let F := B.map π
  let C' := F.map (alternatingGroup (Fin 7)).subtype
  let BN := X.subgroupOf J
  let : Group.IsPerfect X := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY.maximal_faithful.1.1
  let eB : B ≃* X := subgroupOfEquivOfLe hXY.le
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : Group.IsSolvable π.ker := hker ▸ centralPreimage_pCore_isSolvable 2
  have hn : F ≠ ⊥ := by
    intro he
    have hsF : Group.IsSolvable F := by rw [he]; infer_instance
    let : Group.IsSolvable B := (Group.isSolvable_map_iff_of_solvable_ker π B).mp hsF
    exact Chapter1.mem_L_not_isSolvable hlocal
      (Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective)
  have hp : F ≠ ⊤ := proper_image_ne_top hTX hTY hXY hlocal hY.maximal_faithful.1.1 π hker
  have himage : BN.map a = C' := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨π ⟨k,hXY.le hk⟩,mem_map_of_mem π hk,(hres ⟨k,hXY.le hk⟩).symm⟩
    · rintro ⟨x,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨⟨k,(show Y ≤ J from le_sup_left) (hXY.le hk)⟩,hk,hres k⟩
  have hUB : (U : Subgroup (Equiv.Perm (Fin 7))) ≤ normalizer (C' : Set (Equiv.Perm (Fin 7))) := by
    rw [←himage]
    exact (map_mono ((comap_mono hTX).trans
      (le_normalizer_comap J.subtype))).trans (le_normalizer_map a)
  have hgr : g.range = C' ⊔ (U : Subgroup (Equiv.Perm (Fin 7))) := by
    have hg : g.range = (H.subgroupOf J).map a := by
      ext x
      constructor
      · rintro ⟨k,rfl⟩
        exact ⟨⟨k,hHJ k.property⟩,k.property,rfl⟩
      · rintro ⟨k,hk,rfl⟩
        exact ⟨⟨k,hk⟩,rfl⟩
    rw [hg,←C.generates,subgroupOf_sup (hXY.le.trans le_sup_left) le_sup_right,
      Subgroup.map_sup,himage]
    rfl
  have hCg : C' ≤ g.range := hgr.symm ▸ le_sup_left
  have hns : ¬ Group.IsSolvable g.range := by
    intro hsG
    let := hsG
    let j : F →* g.range :=
      ((alternatingGroup (Fin 7)).subtype.comp F.subtype).codRestrict g.range
        (fun x => hCg (mem_map_of_mem _ x.property))
    let : Group.IsSolvable F := Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : g.range => z.val) he)))
    let : Nontrivial F := (nontrivial_iff_ne_bot F).mpr hn
    exact Group.IsPerfect.not_isSolvable F inferInstance
  have hu := (ChapterB.minimalParabolic_surjective_of_not_solvable
    (T.subtype hH.1.1.2) hP
    g.rangeRestrict g.rangeRestrict_surjective hns).1
  let Z := C' ⊔ (U : Subgroup (Equiv.Perm (Fin 7)))
  let eZ : g.range ≃* Z := MulEquiv.subgroupCongr hgr
  let UH := (T.subtype hH.1.1.2).mapSurjective g.rangeRestrict_surjective
  have heU : (UH : Subgroup g.range).map eZ.toMonoidHom =
      (U : Subgroup (Equiv.Perm (Fin 7))).subgroupOf Z := by
    ext x
    constructor
    · rintro ⟨b,⟨k,hk,rfl⟩,rfl⟩
      exact mem_map_of_mem a (show (⟨k,(show (T : Subgroup G) ≤ J from le_sup_right) hk⟩ : J) ∈ (T : Subgroup G).subgroupOf J from hk)
    · intro hx
      obtain ⟨t,ht,he⟩ := hx
      refine ⟨g.rangeRestrict ⟨t,hH.1.1.2 ht⟩,
        mem_map_of_mem g.rangeRestrict ht,?_⟩
      exact Subtype.ext he
  have hu' : Order.HasUniqueMaximalOver
      ((U : Subgroup (Equiv.Perm (Fin 7))).subgroupOf Z) ⊤ := by
    have hh := hu.map eZ.mapSubgroup
    change Order.HasUniqueMaximalOver ((UH : Subgroup g.range).map eZ.toMonoidHom)
      ((⊤ : Subgroup g.range).map eZ.toMonoidHom) at hh
    rwa [heU,map_top_of_surjective _ eZ.surjective] at hh
  obtain ⟨eF⟩ := Theory.SpecificGroups.Alternating.SevenPerfectSylow.five_of_uniqueMaximal F hn hp U hUB hu'
  obtain ⟨q⟩ := Theory.SpecificGroups.Alternating.SevenPerfectSylow.core_five_of_image_five π hπ hker B eF
  exact ⟨(QuotientGroup.congr _ _ eB.symm (pCore_map_iso 2 eB.symm)).trans q⟩

private theorem five_of_alternating_action
    (C : HStarGeneratingComponent T L H X)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (f : H →* alternatingGroup (Fin 7)) (hk : Group.IsSolvable f.ker) :
    Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) := by
  let S := T.subtype hH.1.1.2
  let K := X.subgroupOf H
  let e : K ≃* X := subgroupOfEquivOfLe C.component.1
  let : K.Normal := normal_subgroupOf_of_le_normalizer (by
    rw [←C.generates]
    exact sup_le X.le_normalizer hTX)
  let : Group.IsPerfect X := Chapter1.mem_L_isPerfect (C.exists_maximal_overcomponent hH).1
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let := C.quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm))
  have hgen : K ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le C.component.1]
    change X ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = _
    rw [map_subgroupOf_eq_of_le hH.1.1.2,C.generates,←MonoidHom.range_eq_map,range_subtype]
  have hs : ¬ Group.IsSolvable K := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable (C.exists_maximal_overcomponent hH).1
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  obtain ⟨q⟩ := ChapterB.AlternatingSevenImage.normal_supplement_core_five S
    hP K hgen hs f hk
  exact ⟨(QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans q⟩


/-- The original residual quotient, without a global TI or A₇-exclusion premise. -/
theorem hstar_residual_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨C,Y,hKY,hY⟩ := local_residual_overcomponent h structural modules hZ hH hs
  have hp := local_hstar_minimalParabolic (structural L h).1 hH hs
  have he : Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) := by
    by_cases he : localResidual H = Y
    · have hK : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) := he.symm ▸ hY
      have hp' (J : Subgroup G) (heJ : J = H) (hTJ : (T : Subgroup G) ≤ J) :
          ChapterB.IsMinimalParabolicOver (T.subtype hTJ) ⊤ := by
        subst J
        exact hp
      obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural _ hK).2.1
      exact (E.five_of_minimalParabolic hK ((structural _ hK).2.2 W E).1
        (hp' _ (localResidual_supplement hH.1.1.2) le_sup_right) (modules _ W hK E)).1
    · rcases proper_five_or_alternating_action C structural modules hH hp
          (lt_of_le_of_ne hKY he) hY with hf | ⟨f,hf⟩
      · exact hf
      · exact five_of_alternating_action C hH hp
          (hH.1.1.2.trans (localResidual_normalized H)) f hf
  obtain ⟨e⟩ := he
  let c := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  exact ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourcePointEscape
