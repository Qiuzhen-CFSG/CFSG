module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawThompson
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2ThompsonBorel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelCentralizer

/-!
# The raw original natural rank-one component is impossible

The controlled actual Borel is two-perfect and normalizes J(S)=J(T), so it
lies in M and the marked partner. The literal residual-intersection identity
then makes it centralize V. Its relative-centralizer theorem forces the
original moving subgroup to centralize L, contrary to the source movement.
No marked generation or Case-I data record is assumed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Original raw component controls exclude every natural rank-one block,
without invoking a generation-dependent Case-I source record. -/
theorem PreparedChosenModule.raw_component_not_linear_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (Z1 : Set G)))
    (hlocal : L ∈ Chapter1.L G ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬ L ≤ M)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hmove : ⁅L,⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆⁆ ≠ ⊥) :
    ¬ ∃ n : ℕ, IsL2EvenBlock L n := by
  let := h.elementary
  rintro ⟨n,hb⟩
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let R := (pResidual 2 (M ⊓ H : Subgroup G)).map (M ⊓ H).subtype
  let W := ⁅V,R⁆
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  have hSM : S ≤ H ⊓ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨hx.2,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x hx.1).symm)⟩
  have hH : IsSQTK KnownSimple.IsKnownSimple H := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hlocal
  have hPK : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  let B := (normalizer (P : Set L)).map L.subtype
  have hBMZ : B ≤ H ⊓ Mc := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype ≤ _
    rw [hPK]
    exact raw_component_borel_le_marked H Mc S L hH hSM hS hSyl hL hlocal hq
      hout hcontrol hbound hb
  have hJN := (h.raw_component_thompson hG T hM hJ hu hZ ⟨hL.1,hlocal⟩ hq
    hb.2.1.fitting hout houtM).1
  have hBJ : B ≤ normalizer (elementaryAbelianMaxJ S : Set G) :=
    hb.borel_normalizes_thompson L S hS P (hP.le.trans inf_le_left) hJN
  have hJS := (h.caseI_marked_thompson_control hG T hM hJ hZ).1
  have hNJ := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  have hBM : B ≤ M := by
    change B ≤ normalizer (elementaryAbelianMaxJ S : Set G) at hBJ
    change elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) at hJS
    rw [hJS] at hBJ
    exact hBJ.trans hNJ
  have hBtwo : IsPPerfect 2 B := (hb.borel_twoPerfect P).of_surjective
    ((normalizer (P : Set L)).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom
    ((normalizer (P : Set L)).equivMapOfInjective L.subtype L.subtype_injective).surjective
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
    (hb.relative_borel_centralizer H L S hL.1 inf_le_right hL.2 hS P)
  apply hmove
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hWL

end CFSG.Quasithin.Chapter15.Section01
