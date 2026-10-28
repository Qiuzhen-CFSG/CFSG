module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointFFSource
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels

/-!
# Thompson movement in the original tensor point action

The source point Sylow contains the original Thompson subgroup, and
Thompson heredity identifies their elementary Thompson subgroups. On the
literal orbit U=⟨Ω₁Z(T)^I⟩, movement therefore supplies an FF action and
makes the actual component image quasisimple. The complete B.5.1 theorem
applies to that same quotient action and its offender subgroup.

These are the FF entrance statements in Aschbacher--Smith 9.4.1,
printed p.735. The nonmovement and natural-cover contradictions remain
separate source steps.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open ChapterB.InternalThompsonAction Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Thompson movement classifies the literal point-component action,
with the orbit, quotient map, component image and offender actor retained. -/
theorem tensorPoint_centerOrbit_ff_models (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G}
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (hr : IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I).subgroupOf
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I : Set G)) :
    let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
    let W := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I).subgroupOf H
    letI := hr.normal; letI := hr.elementary
    let ρ := action W
    let N := offenderSubgroup ρ
    IsFFModule ρ ∧ IsQuasisimple ((I.subgroupOf H).map (actionMk W)) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((I.subgroupOf H).map (actionMk W)).subgroupOf N)) := by
  let X := centralizer ({(v : G)} : Set G)
  let R := (T : Subgroup G) ⊓ X
  let H := I ⊔ R
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I
  let W := U.subgroupOf H
  let := hr.normal
  let := hr.elementary
  have hHX : H ≤ X := sup_le hIX inf_le_right
  have hSyl : Chapter1.IsSylowIn 2 R H :=
    (m.tensor_centralizer_sylow v.property hs).restrict le_sup_right hHX
  obtain ⟨P,hP⟩ := hSyl
  change (P : Subgroup H).map H.subtype = R at hP
  have hPR : (P : Subgroup H) = R.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)]
  let K := I.subgroupOf H
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hHX.trans hIN)
  have hK : K.IsCComponent := hI.subgroupOf_of_le le_sup_left hHX
  have hKP : K ⊔ (P : Subgroup H) = ⊤ := by
    rw [hPR]
    exact (codisjoint_subgroupOf_sup I R).eq_top
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R :=
    le_inf (sSup_le fun _ h => h.1)
      (m.thompson_centralizes_fullModule.trans
        (centralizer_le (Set.singleton_subset_iff.mpr v.property)))
  have hJP : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    exact elementaryAbelianMaxJ_eq_of_intermediate_finite _ _ hJR inf_le_left
  have hUH : U ≤ H := by
    apply conjugateSpanBy_le ?_ (le_sup_left.trans H.le_normalizer)
    intro z hz
    have hz' := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact mem_sup_right ⟨hz'.1,mem_centralizer_singleton_iff.mpr
      (hz'.2.2 v (m.fullModule_le_sylow v.property)).symm⟩
  have hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
    intro hc
    apply hm
    intro j hj u hu
    obtain ⟨a,ha,rfl⟩ := hJP.symm ▸ hj
    exact congrArg H.subtype (hc ha ⟨u,hUH hu⟩ hu)
  have hp : IsPGroup 2 (zpowers (v : G)) :=
    T.isPGroup'.to_le (zpowers_le.mpr (m.fullModule_le_sylow v.property))
  have hne : zpowers (v : G) ≠ ⊥ := by
    intro he
    exact m.tensorPoint_ne_one v hv (mem_bot.mp (he ▸ mem_zpowers _))
  have hHN : H ≤ normalizer (zpowers (v : G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact hHX
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    have hn := D.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal (normalizer (zpowers (v : G) : Set G)) from ⟨_,hne,hp,rfl⟩)
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp (hn.subgroup (H.subgroupOf _))
  refine ⟨isFFModule_of_thompson_movement P W hmove,?_,?_⟩
  · exact quasisimple_of_thompson_movement
      ChapterB.SourceInduction.adequateClassification_knownSimple hH P K W hK hKP
      hr.quotient_pCore_eq_bot hmove
  · exact quasisimple_source_conclusion_of_thompson_movement hH P K W hK hKP
      hr.quotient_pCore_eq_bot hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
