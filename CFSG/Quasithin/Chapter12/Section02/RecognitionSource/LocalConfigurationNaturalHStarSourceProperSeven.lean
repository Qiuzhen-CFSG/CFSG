module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperEight
public import Theory.SpecificGroups.Alternating.SevenCharacteristicExtension
public import Theory.SpecificGroups.Alternating.SevenPerfectSylow
public import Theory.SpecificGroups.Alternating.SevenPerfectSylowLift
public import Theory.SpecificGroups.Alternating.SevenComponent.PointSix
public import Theory.GroupTheory.PCoreCentralPreimageRestriction
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel

/-!
# The actual seven-letter H-star action

The characteristic O₂,Z quotient extends to the original YT, preserving its
marked projection and with solvable kernel. In the full symmetric image,
minimal parabolicity identifies the proper residual image as A₅; central
cover rigidity then identifies the intrinsic X/O₂(X). In the alternating
image we retain the actual homomorphism and its solvable kernel for the
small elementary-subgroup argument in 12.2.18.

Source: Aschbacher–Smith, 12.2.7 and 12.2.18, printed pp.797–801.
This does not yet identify the residual in the alternating-image case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H X Y : Subgroup G}

private theorem map_centralPreimage_core {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) :
    (centralPreimage (pCore 2 A)).map e.toMonoidHom = centralPreimage (pCore 2 B) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply centralPreimage_pCore_comap_le 2 e.symm.toMonoidHom e.symm.injective
    change e.symm (e x) ∈ centralPreimage (pCore 2 A)
    rw [e.symm_apply_apply]
    exact hx
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply centralPreimage_pCore_comap_le 2 e.toMonoidHom e.injective
    simpa only [mem_comap,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using hy

private theorem seven_join_action
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (e : (Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) :
    ∃ (π : Y →* alternatingGroup (Fin 7))
      (a : (Y ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 7)),
      Function.Surjective π ∧ π.ker = centralPreimage (pCore 2 Y) ∧
      (∀ y : Y, a (inclusion le_sup_left y) = (π y).val) ∧
      alternatingGroup (Fin 7) ≤ a.range ∧ Group.IsSolvable a.ker := by
  let J := Y ⊔ (T : Subgroup G)
  let A := Y.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hTY)
  let d : A ≃* Y := subgroupOfEquivOfLe le_sup_left
  let N := centralPreimage (pCore 2 A)
  let eA : (A ⧸ N) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr _ _ d (map_centralPreimage_core d)).trans e
  obtain ⟨a,ha⟩ := alternatingGroup.SevenComponent.exists_characteristic_extension A N eA
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 Y)))
  have hres (y : Y) : a (inclusion le_sup_left y) = (π y).val :=
    ha (d.symm y)
  let U := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hgen : A ⊔ (U : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left]
    change Y ⊔ ((T : Subgroup G).subgroupOf J).map J.subtype = _
    rw [map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  let : Group.IsSolvable N := centralPreimage_pCore_isSolvable 2
  have htwo : IsPGroup 2 (J ⧸ A) := quotient_isPGroup_of_sup_eq_top
    (U : Subgroup J) A U.isPGroup' ((sup_comm _ _).trans hgen)
  let : Group.IsNilpotent (J ⧸ A) := htwo.isNilpotent
  refine ⟨π,a,e.surjective.comp (QuotientGroup.mk'_surjective _),?_,hres,?_,
    alternatingGroup.SevenComponent.characteristic_extension_kernel_solvable A N eA a ha⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  · rw [←alternatingGroup.SevenComponent.characteristic_extension_image A N eA a ha]
    exact map_le_range _ _

private theorem proper_image_ne_top
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hXY : X < Y) (hX : X ∈ Chapter1.L G (T : Subgroup G))
    (hY : Y ∈ Chapter1.L G (T : Subgroup G))
    (π : Y →* alternatingGroup (Fin 7))
    (hk : π.ker = centralPreimage (pCore 2 Y)) :
    (X.subgroupOf Y).map π ≠ ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B := X.subgroupOf Y
  let : Group.IsPerfect X := Chapter1.mem_L_isPerfect hX
  let : Group.IsPerfect Y := Chapter1.mem_L_isPerfect hY
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXY.le).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXY.le).symm.surjective
  obtain ⟨U,hU⟩ := (T.subtype
    (show (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show Y ≤ Y ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le Y.le_normalizer hTY)
  have hU' : (U : Subgroup Y).map Y.subtype = (T : Subgroup G) ⊓ Y := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hU
  have hUT : (U : Subgroup Y) ≤ (T : Subgroup G).subgroupOf Y := by
    intro x hx
    exact (show (x : G) ∈ (T : Subgroup G) ⊓ Y from
      hU' ▸ mem_map_of_mem Y.subtype hx).1
  have hUB : (U : Subgroup Y) ≤ normalizer (B : Set Y) :=
    (hUT.trans (comap_mono hTX)).trans (le_normalizer_comap Y.subtype)
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
  intro he
  have ht : (⊤ : Subgroup Y) ≤ B :=
    perfect_le_of_map_le_of_kernel_central_mod_solvable π (pCore 2 Y)
      (hk.symm ▸ le_centralPreimage _)
      (by rw [hk]; exact map_comap_le _ _) ⊤ B
      ((pCore_isPGroup.le_sylow_of_normal U).trans hUB)
      (by rw [he]; exact le_top)
  exact hXY.not_ge (subgroupOf_eq_top.mp (top_unique ht))

/-- A proper A₇ overcomponent supplies either the actual A₅ residual quotient
or an actual seven-letter alternating action of H with solvable kernel. -/
theorem HStarGeneratingComponent.proper_five_or_alternating_action_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X < Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) :
    Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) ∨
      ∃ f : H →* alternatingGroup (Fin 7), Group.IsSolvable f.ker := by
  have hTX := C.normalized_of_overcomponent_at structural modules hH hXY.le hY
  have hTY := (structural Y hY).1
  have hlocal := (C.exists_maximal_overcomponent hH).1
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
  obtain ⟨⟨e⟩,_⟩ := C.proper_seven_source_at h D structural modules hTI hH hXY hY E
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
    (T.subtype hH.1.1.2) (chosen_hstar_minimalParabolic_at h D structural hTI hH)
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

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
