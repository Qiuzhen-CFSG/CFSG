module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBenderBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import Theory.SpecificGroups.PSL2.ThompsonBorel
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# Original ordinary binary linear exclusions

For degree greater than two, the actual marked Borel, component-orbit
Thompson theorem and relative centralizer calculation contradict original
residual control. In degrees two and three the original faithful elementary
sixteen exceeds the native full-automorphism two-rank. All groups and actors
are the original source objects; no whole-M generation is introduced.
The private raw Thompson contradiction is intentionally shared with the
unitary companion through an internal import.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

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

private theorem raw_bender_thompson_contradiction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hmove : ⁅L,⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆⁆ ≠ ⊥)
    {B : Subgroup G} (hBMZ : B ≤ centralizer (Z1 : Set G) ⊓ Mc)
    (hBJ : B ≤ normalizer (elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Set G))
    (hBtwo : IsPPerfect 2 B)
    (hfix : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ centralizer (B : Set G) ≤
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ centralizer (L : Set G)) : False := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let R := (pResidual 2 (M ⊓ H : Subgroup G)).map (M ⊓ H).subtype
  let W := ⁅V,R⁆
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

/-- Original controls exclude every binary linear ordinary component of
degree greater than two, retaining its literal component orbit and Borel. -/
theorem PreparedChosenModule.raw_ordinary_not_binary_linear_gt_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
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
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hmove : ⁅L,⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆⁆ ≠ ⊥)
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    {n : ℕ} (hn : 2 < n) (hm : ClassicalGroup.IsPSL L 2 (2^n)) : False := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  have hBMZ : B ≤ H ⊓ Mc := by
    have he := h.raw_ordinary_bender_borel hG T hu hZ hZne hLG hL
      hSylG hSylL hcontrol hbound hout (.linear n (by omega) hm)
    change (H ⊓ Mc) ⊓ L = B at he
    rw [←he]
    exact inf_le_left
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨P,hP⟩ := hSylL
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hBJ := Theory.PSL2.OrdinaryBorel.component_normalizer_thompson_field H L S hLG inf_le_right hL
    (T.isPGroup'.to_le inf_le_left) (raw_ordinary_component_relIndex H S L hsq hLG inf_le_right hL)
    P (hP ▸ inf_le_left) hn hF e
  change (normalizer ((P : Subgroup L) : Set L)).map L.subtype ≤ _ at hBJ
  rw [hP'] at hBJ
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let B0 := normalizer (P : Set L)
  have hBQ : B0.map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) :=
    map_equiv_normalizer_eq (P : Subgroup L) e
  let eB : B0 ≃* normalizer (Q : Set PSL(2,F)) :=
    (e.subgroupMap B0).trans (MulEquiv.subgroupCongr hBQ)
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact (by decide : 4=2^2) ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hb : IsPPerfect 2 B0 := (Theory.PSL2.OrdinaryBorel.normalizer_twoPerfect hq Q).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hBtwo : IsPPerfect 2 B := by
    have hh := hb.of_surjective (L.subtype.subgroupMap B0) (L.subtype.subgroupMap_surjective B0)
    change IsPPerfect 2 ((normalizer ((P : Subgroup L) : Set L)).map L.subtype) at hh
    rwa [hP'] at hh
  have hfix : S ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (L : Set G) := by
    have hc := Theory.PSL2.OrdinaryBorel.relative_centralizer H L hLG hL hF (by omega) e P
    change H ⊓ centralizer ((normalizer ((P : Subgroup L) : Set L)).map L.subtype : Set G) ≤ _ at hc
    rw [hP'] at hc
    exact le_inf inf_le_left ((inf_le_inf_right _ (show S ≤ H from inf_le_right)).trans hc)
  exact raw_bender_thompson_contradiction hG T hM hJ h hZ hI hmove hBMZ hBJ hBtwo hfix

/-- The original faithful sixteen excludes the small binary fields, including
the exceptional L₂(4) row, in the correct automorphism-action direction. -/
theorem PreparedChosenModule.decomposable_five_raw_not_binary_linear_small
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z1 : Set G)
      let R := (pResidual 2 C).map C.subtype
      ∀ {L : Subgroup G}, R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) → ⁅L,⁅V,R⁆⁆ ≠ ⊥ →
        ∀ n : ℕ, 2 ≤ n → n ≤ 3 → ¬ ClassicalGroup.IsPSL L 2 (2^n) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 C R L hnL hmove n hn hnsmall hm
  obtain ⟨hBL,_,hcard⟩ := h.decomposable_five_raw_moving_support_action
    hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive hnL hmove
  let B := plane V (c.ambientFactor d s.second).space
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (plane_le _)
  let : IsElementaryAbelian 2 (internalActionImage B L hBL) :=
    IsElementaryAbelian.of_surjective (actionHom B L hBL).rangeRestrict
      (actionHom B L hBL).rangeRestrict_surjective
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let A := (internalActionImage B L hBL).map (MulAut.congr e).toMonoidHom
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hh := (primeRank_le_iff_elementary_card_le (MulAut PSL(2,F))).mp
    (Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hn hF) A hA
  have hcardA : Nat.card A = 16 := by
    rw [card_map_of_injective (MulAut.congr e).injective]
    exact hcard
  have hpw : 2^n ≤ 8 := by
    exact Nat.pow_le_pow_right (by decide) hnsmall
  rw [hcardA] at hh
  omega

end CFSG.Quasithin.Chapter15.Section01
