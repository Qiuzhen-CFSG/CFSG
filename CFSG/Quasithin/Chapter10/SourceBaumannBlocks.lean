module
public import CFSG.Quasithin.Chapter10.SourceLocalParabolicAction
public import CFSG.Quasithin.Chapter10.SourceA5BlockIdentification
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ComponentBlockSource
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The original alternating-five block in the Baumann exception

If the Baumann normalizer escapes the unique maximal two-local M above
L₀T, no nontrivial characteristic subgroup of Baum(T) is normal in L₀T.
The original reduced local module and characteristic-two structure therefore
meet every premise of the completed E.2.3 block theorem. Its actual marked
symmetric-five alternatives produce a generating alternating-five block.
C-component orbit correspondence identifies the original L with a Sylow
conjugate of that block.

The original block is subnormal inside L₀T, where it was constructed;
its alternating-five action is also retained on the intrinsic original L.
No equality of the local and full modules, characteristic-control premise,
or independently chosen replacement component is assumed.
Source: Aschbacher–Smith, the opening of 10.2.1's A₅ case, printed p.742,
using E.2.3(4) and C.1.24, printed pp.217 and130–131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

omit D [Finite G] in
private theorem normalizer_mapped_characteristic
    {P : Type*} [Group P] (C : Subgroup P) (F : Subgroup C) [F.Characteristic]
    (i : P →* G) (hi : Function.Injective i) :
    normalizer (C.map i : Set G) ≤ normalizer ((F.map C.subtype).map i : Set G) := by
  let e := C.equivMapOfInjective i hi
  let K := F.map e.toMonoidHom
  have hK : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : (F.map C.subtype).map i = K.map (C.map i).subtype := by
    rw [map_map, map_map]
    rfl
  rw [he]
  exact normalizer_le_normalizer_characteristic_image (C.map i) K

/-- The full ambient Baumann normalizer forces the exact characteristic-subgroup
vanishing premise of E.2.3 in the original local join. -/
theorem source_baumann_characteristic_normal_eq_bot
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    let S := T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)
    ∀ R : Subgroup (ChapterB.baumann (S : Subgroup (localJoin T L))),
      R.Characteristic →
      (R.map (ChapterB.baumann (S : Subgroup (localJoin T L))).subtype).Normal → R = ⊥ := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let B := ChapterB.baumann (S : Subgroup H)
  change ∀ R : Subgroup B, R.Characteristic → (R.map B.subtype).Normal → R = ⊥
  intro R hc hn
  by_contra hne
  let := hc
  let := hn
  let W := (R.map B.subtype).map H.subtype
  have hbmap : B.map H.subtype = ChapterB.baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change B.map H.subtype = ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
    exact he.trans (congrArg ChapterB.baumann (map_subgroupOf_eq_of_le le_sup_right))
  have hW : IsPGroup 2 W :=
    (((S.isPGroup'.to_le (show B ≤ (S : Subgroup H) from inf_le_left)).to_subgroup R).map
      B.subtype).map H.subtype
  have hneW : W ≠ ⊥ := by
    intro he
    exact hne ((R.map_eq_bot_iff_of_injective B.subtype_injective).mp
      (((R.map B.subtype).map_eq_bot_iff_of_injective H.subtype_injective).mp he))
  have hHW : H ≤ normalizer (W : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg w hw
    obtain ⟨v,hv,rfl⟩ := hw
    exact mem_map.mpr ⟨⟨g,hg⟩ * v * ⟨g,hg⟩⁻¹,
      (inferInstance : (R.map B.subtype).Normal).conj_mem v hv ⟨g,hg⟩, rfl⟩
  apply hout
  have hNW := normalizer_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness (source_uniqueness D)).2.2 hW hneW hHW
  have hN := normalizer_mapped_characteristic B R H.subtype H.subtype_injective
  rw [hbmap] at hN
  exact hN.trans hNW

/-- The original local join has characteristic two by condition (E). -/
theorem source_join_fitting :
    generalizedFitting (localJoin T L) = pCore 2 (localJoin T L) := by
  have hH : localJoin T L ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, show (T : Subgroup G) ≤ localJoin T L from le_sup_right⟩
    exact fun he => D.module_ne_bot (bot_unique (D.module_le_core.trans_eq he))
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (D.simpleQTKE.evenCharacteristic T) hH))

/-- The original local component makes its local join nonsolvable. -/
theorem source_join_not_solvable : ¬ Group.IsSolvable (localJoin T L) := by
  intro hs
  let := hs
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  exact Chapter1.mem_L_not_isSolvable D.maximal.1
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hLH))
/-- The exact marked symmetric-five action constructs an actual generating
A₅ block inside the original local join. -/
theorem source_five_action_generating_block_with_module
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤)
    (hfive : SourceFiveAction D)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ K : Subgroup (localJoin T L), K.IsCComponent ∧ ChapterC.IsBlock K ∧
      ChapterC.IsAlternatingBlock K 5 ∧
      K ⊔ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) :
        Subgroup (localJoin T L)) = ⊤ ∧
      (ChapterC.blockU K).map K.subtype ≤ D.moduleSubgroup.subgroupOf (localJoin T L) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  have hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) :=
    fun h => hout (source_local_baumann_normalizer_le_of_centralizes D h)
  have hmove : ¬ elementaryAbelianMaxJ (S : Subgroup H) ≤ centralizer (U : Set H) := by
    intro hc
    apply hJ
    have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le le_sup_right)
    rw [← hjmap]
    rintro g ⟨j, hj, rfl⟩ z hz
    exact congrArg H.subtype (hc hj
      ⟨z, (D.module_le_core.trans (pCoreIn_le 2 H)) hz⟩ hz)
  have hG := (D.local_internal_module (source_uniqueness D)).sqtk
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hno := source_baumann_characteristic_normal_eq_bot D hout
  rcases hfive with ⟨hqs,c,⟨e⟩⟩ | ⟨d,t,ht1,ht2,⟨c⟩⟩
  · obtain ⟨hb,ha,_,_,hUm⟩ := quasisimple_five_block_of_no_characteristic_baumann
      h36 hG S hP U hU hmove q hq hk hqs c.sectionData e (source_join_fitting D) hno
    have hgen := pResidual_sup_sylow_eq_top S
    exact ⟨pResidual 2 H,
      nonsolvable_generating_block_isCComponent (source_join_not_solvable D) _ hb S hgen,
      hb,ha,hgen,hUm⟩
  · obtain ⟨K,hb,ha,_,_,hUm,hgen⟩ := paired_five_block_of_no_characteristic_baumann
      h36 hG S hP U hU hmove q hq hk (source_join_not_solvable D)
      (source_join_fitting D) d c ⟨t,ht1,ht2⟩ hno
    exact ⟨K,nonsolvable_generating_block_isCComponent
      (source_join_not_solvable D) K hb S hgen,hb,ha,hgen,hUm⟩

/-- The generating block conclusion with its internal component membership. -/
theorem source_five_action_generating_block
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤)
    (hfive : SourceFiveAction D)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ K : Subgroup (localJoin T L), K.IsCComponent ∧ ChapterC.IsBlock K ∧
      ChapterC.IsAlternatingBlock K 5 ∧
      K ⊔ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) :
        Subgroup (localJoin T L)) = ⊤ := by
  obtain ⟨K,hK,hb,ha,hgen,_⟩ :=
    source_five_action_generating_block_with_module D hP hfive hout
  exact ⟨K,hK,hb,ha,hgen⟩

/-- The original L is an alternating-five block whenever the Baumann
normalizer is not contained in M. The block is ambient in L₀T. -/
theorem source_a5_original_block_of_baumann_not_controlled
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∧
      ChapterC.IsAlternatingBlock (L.subgroupOf (localJoin T L)) 5 ∧
      ChapterC.IsAlternatingBlock L 5 := by
  have hfive := (source_a5_baumann_normalizer_or_five_action_unconditional D e hn).resolve_left hout
  obtain ⟨K,hK,hb,ha,hgen⟩ := source_five_action_generating_block D
    (source_a5_minimal_parabolic D e hn) hfive hout
  exact original_L_block_of_generating_block D K hK hgen hb ha
end CFSG.Quasithin.Chapter10
