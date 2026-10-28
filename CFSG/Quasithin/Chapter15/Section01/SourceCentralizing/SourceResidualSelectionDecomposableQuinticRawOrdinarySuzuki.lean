module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinarySolvableBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawLinearTwo
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.SpecificGroups.Suzuki.ComponentThompson
public import Theory.SpecificGroups.Suzuki.BorelCover
public import Theory.SpecificGroups.Suzuki.BorelResidualCentralizer
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# The original ordinary simple Suzuki row

Native Suzuki root centralizers and the unique proper Sylow overgroup give
characteristic two and solvability for the actual Borel. The original local
normalizer controls identify the marked intersection with that Borel.
The component-orbit bound and native Thompson and centralizer geometry then
contradict the original moving support. No whole-M generation or global
residual centralization is assumed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

private theorem raw_suzuki_sylow_selfCentralizing
    {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 0 < m)
    (e : X ≃* SuzukiMatrixGroup m) (P : Sylow 2 X) :
    centralizer (P : Set X) ≤ P := by
  have hcard : 1 < Nat.card (SuzukiRootSubgroup m) := by
    rw [suzukiRootSubgroup_card m hm]
    exact one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by decide)
  let : Nontrivial (SuzukiRootSubgroup m) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨x,hx⟩ := exists_ne (1 : SuzukiRootSubgroup m)
  have hxne : (x : SuzukiMatrixGroup m) ≠ 1 := fun hh => hx (Subtype.ext hh)
  have hc : centralizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ≤
      SuzukiRootSubgroup m :=
    (centralizer_le (Set.singleton_subset_iff.mpr x.property)).trans
      (suzukiRootSubgroup_centralizer_le m hm x.property hxne)
  obtain ⟨f,hP,_⟩ := suzukiSylow_aligned_equiv hm e P
  intro y hy
  rw [←hP,mem_map_equiv]
  apply hc
  intro z hz
  apply f.injective
  simpa only [map_mul,f.apply_symm_apply] using hy (f z)
    (by
      change f z ∈ (P : Subgroup X)
      rw [←hP]
      exact mem_map_of_mem f.toMonoidHom hz)

private theorem raw_suzuki_borel_characteristicTwo
    (S L : Subgroup G) (hSyl : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    {m : ℕ} (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) :
    HasCharacteristicTwo ((normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype) := by
  obtain ⟨P,hP⟩ := hSyl
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  let B0 := normalizer (P : Set L)
  have hb : HasCharacteristicTwo B0 := centralizer_pCore_le_of_normalized 2
    (P : Subgroup L) B0 P.isPGroup' (P : Subgroup L).le_normalizer le_rfl
    (raw_suzuki_sylow_selfCentralizing hm e P)
  have hh := hb.of_equiv (B0.equivMapOfInjective L.subtype L.subtype_injective)
  change HasCharacteristicTwo ((normalizer ((P : Subgroup L) : Set L)).map L.subtype) at hh
  rwa [hP'] at hh

private theorem raw_ordinary_component_relIndex
    (H S L : Subgroup G) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hLG : L ≤ H) (hSH : S ≤ H) (hL : IsComponent H (L.subgroupOf H)) :
    (normalizer (L : Set G)).relIndex S ≤ 2 := by
  have hi : (normalizer (L.subgroupOf H : Set H)).index ≤ 2 := by
    rcases hL.normal_or_index_two_of_odd_rank_le_two hH.stronglyQuasithin with hn | hn
    · rw [normalizer_eq_top_iff.mpr hn,index_top]
      decide
    · exact hn.le
  have hr : (normalizer (L.subgroupOf H : Set H)).relIndex (S.subgroupOf H) ≤
      (normalizer (L.subgroupOf H : Set H)).index := by
    simpa only [relIndex_top_right] using
      (relIndex_le_of_le_right (show S.subgroupOf H ≤ ⊤ from le_top) index_ne_zero_of_finite
        (H := normalizer (L.subgroupOf H : Set H)))
  have hh := hr.trans hi
  rw [←subgroupOf_normalizer_eq hLG,relIndex_subgroupOf hSH] at hh
  exact hh

/-- Original local controls identify the proper marked intersection in the
same simple Suzuki component with its full Borel. -/
theorem PreparedChosenModule.raw_ordinary_suzuki_borel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    {m : ℕ} (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) :
    ((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L) =
      (normalizer ((((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L).subgroupOf L : Set L)).map
        L.subtype := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let A := (H ⊓ Mc) ⊓ L
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  have hSM : S ≤ H ⊓ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨hx.2,hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz x hx.1).symm)⟩
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hf := (ChapterF.Source.IsRankOneModel.suzuki m ⟨e⟩).rankOneSylowFacts P
  have hproper : A.subgroupOf L < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hout
    intro x hx
    have hh : (⟨x,hx⟩ : L) ∈ A.subgroupOf L := he ▸ mem_top _
    exact hh.1
  have hPA : (P : Subgroup L) ≤ A.subgroupOf L := by
    intro x hx
    have hh := hP ▸ mem_map_of_mem L.subtype hx
    exact ⟨hSM hh.1,hh.2⟩
  have hsol : Group.IsSolvable A := by
    let : Group.IsSolvable (normalizer (P : Set L)) := hf.solvable
    let : Group.IsSolvable (A.subgroupOf L) := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (hf.unique_maximal _ hPA hproper))
    exact Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe (show A ≤ L from inf_le_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show A ≤ L from inf_le_right)).surjective
  have hc : SolvableSylowControl 2 L := by
    intro Q D hD hQD
    let := hD
    have hnot : ¬ Group.IsSolvable L := by
      intro hh
      let := hh
      exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
        (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
    have hDproper : D < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro he
      subst D
      exact hnot (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := L)).toMonoidHom)
        (Subgroup.topEquiv (G := L)).surjective)
    exact ((ChapterF.Source.IsRankOneModel.suzuki m ⟨e⟩).rankOneSylowFacts Q).unique_maximal
      D hQD hDproper
  exact raw_ordinary_solvable_borel_eq H Mc S L
    (caseI_centralizer_sqtk hG Z1 hZne ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left)))
    hSM (T.isPGroup'.to_le inf_le_left) hSylG hLG hL ⟨P,hP⟩ hcontrol hbound hsol hc
    (raw_suzuki_borel_characteristicTwo S L ⟨P,hP⟩ hm e)

/-- The original ordinary component cannot be any nondegenerate simple
Suzuki model. This retains the actual component and literal residual intersection. -/
theorem PreparedChosenModule.raw_ordinary_not_suzuki
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hmove : ⁅L,⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆⁆ ≠ ⊥)
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    {m : ℕ} (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) : False := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let R := (pResidual 2 (M ⊓ H : Subgroup G)).map (M ⊓ H).subtype
  let W := ⁅V,R⁆
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  let : IsQuasisimple (L.subgroupOf H) := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup L := e.isSimpleGroup
  have hz : center L = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp hh))
  have hcore : pCore 2 L = ⊥ := hcenter.symm.trans hz
  let eq : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e
  have hBMZ : B ≤ H ⊓ Mc := by
    have he := h.raw_ordinary_suzuki_borel hG T hu hZ hZne hLG hL
      hSylG hSylL hcontrol hbound hout hm e
    change (H ⊓ Mc) ⊓ L = B at he
    rw [←he]
    exact inf_le_left
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hBJ := suzuki_component_borel_normalizes_thompson H L S hLG inf_le_right hL
    (T.isPGroup'.to_le inf_le_left) (raw_ordinary_component_relIndex H S L hsq hLG inf_le_right hL)
    P (hP ▸ inf_le_left) hm e
  change (normalizer ((P : Subgroup L) : Set L)).map L.subtype ≤ _ at hBJ
  rw [hP'] at hBJ
  have hb := suzuki_coverBorel_isPPerfect hcenter.ge hm eq P
  have hBtwo : IsPPerfect 2 B := by
    have hh := hb.of_surjective (L.subtype.subgroupMap (normalizer (P : Set L)))
      (L.subtype.subgroupMap_surjective _)
    change IsPPerfect 2 ((normalizer ((P : Subgroup L) : Set L)).map L.subtype) at hh
    rwa [hP'] at hh
  have hfix : S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G) := by
    have hc := suzuki_borelResidual_relative_centralizer H L hLG hL hcenter hm eq P
    rw [(pResidual_eq_top_iff 2 _).mpr hb,←MonoidHom.range_eq_map,range_subtype] at hc
    change H ⊓ centralizer ((normalizer ((P : Subgroup L) : Set L)).map L.subtype : Set G) ≤ _ at hc
    rw [hP'] at hc
    exact le_inf inf_le_left ((inf_le_inf_right _ (show S ≤ H from inf_le_right)).trans hc)
  have hJS := (h.caseI_marked_thompson_control hG T hM hJ hZ).1
  have hNJ := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  have hBM : B ≤ M := by
    change B ≤ normalizer (elementaryAbelianMaxJ S : Set G) at hBJ
    change elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) at hJS
    rw [hJS] at hBJ
    exact hBJ.trans hNJ
  have hBI : B ≤ M ⊓ Mc ⊓ H :=
    le_inf (le_inf hBM (hBMZ.trans inf_le_right)) (hBMZ.trans inf_le_left)
  have hBV : B ≤ centralizer (V : Set G) := by
    have hh := embedded_pResidual_mono 2 hBI
    rw [(pResidual_eq_top_iff 2 B).mpr hBtwo,←MonoidHom.range_eq_map,range_subtype,hI] at hh
    exact hh.trans ((map_subtype_le _).trans inf_le_right)
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  have hWS : W ≤ S := hWV.trans (le_inf hVT
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left))))
  have hWB := hWV.trans (le_centralizer_iff.mp hBV)
  have hWL : W ≤ centralizer (L : Set G) := (le_inf hWS hWB).trans
    (hfix.trans inf_le_right)
  apply hmove
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hWL

end CFSG.Quasithin.Chapter15.Section01
