module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightFrattiniPairs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCentralFour
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs.SubgroupTransport

/-!
# The literal distance-eight center and its natural summand

Transport through the component embedding identifies both the complete center
and its fixed factor. Commutator functoriality then identifies [Z(Q),L] with
the source U, giving the direct decomposition and its natural module action
under the same CommonFacts marking as the three Frattini sections.

The whole fixed-factor equality additionally identifies C_Q(L) with the source
four-group in the original group. Its elementarity and order follow from the
existing source calculation. Centrality in the original group is a separate
obligation; it is not inferred from centrality in the replacement.

The literal SmallMSPair consumer is LinearThree/DistanceEightSourceSections.
The fixed-factor premise belongs to qt-ms93-distance-eight-fixed-factor;
qt-rank-two-ms93 retains original centrality, the radical-centralizer inequality,
and final C.1.34 assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(iii)--(iv), printed p.895;
Aschbacher--Smith C.1.34(4), printed pp.136--137.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
open DistanceEight.CoreFactors
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
  {h : Input κ L R} (s : InputSetup h)
  (common : CommonFacts s.reduction.radical s.source s.geometry)

private theorem map_fixed {A B : Type*} [Group A] [Group B]
    (D : Subgroup A) (f : A →* B) (hf : Function.Injective f) :
    (D ⊓ center A).map f = D.map f ⊓ centralizer (f.range : Set B) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨mem_map_of_mem f hy.1, ?_⟩
    rintro z ⟨a,rfl⟩
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hy.2 a)
  · rintro ⟨⟨y,hy,rfl⟩,hc⟩
    refine ⟨y,⟨hy,mem_center_iff.mpr ?_⟩,rfl⟩
    intro a
    apply hf
    simpa only [map_mul] using hc (f a) ⟨a,rfl⟩

private theorem componentEmbedding_range : s.componentEmbedding.range =
    Ltilde s.reduction.radical (alpha s.reduction.radical) := by
  rw [s.Ltilde_embedded]
  change ((embedM s.reduction.radical).comp
    (inclusion (show L ≤ s.reduction.overgroup from le_sup_left))).range = _
  rw [MonoidHom.range_comp]
  congr 1
  ext x
  exact ⟨fun ⟨l,hl⟩ => hl ▸ l.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩

private theorem intrinsic_center_image :
    (sCenter (blockU L)).map s.componentEmbedding =
      sCenter (core s.reduction.radical (alpha s.reduction.radical)) := by
  rw [← centerIn_map _ _ s.componentEmbedding_injective,s.intrinsic_core_image]

private theorem intrinsic_fixed_image :
    (blockU L ⊓ center L).map s.componentEmbedding =
      core s.reduction.radical (alpha s.reduction.radical) ⊓
        centralizer (Ltilde s.reduction.radical (alpha s.reduction.radical) :
          Set (FreeAmalgam s.reduction.radical)) := by
  rw [map_fixed _ _ s.componentEmbedding_injective,s.intrinsic_core_image,
    s.componentEmbedding_range]

include common in
private theorem intrinsic_moved_image
    (earlier : Earlier s.reduction.radical s.geometry) :
    (⁅sCenter (blockU L), (⊤ : Subgroup L)⁆).map s.componentEmbedding =
      U s.reduction.radical (alpha s.reduction.radical) := by
  rw [map_commutator,s.intrinsic_center_image,← MonoidHom.range_eq_map,
    s.componentEmbedding_range]
  apply le_antisymm
  · exact commutator_mono (Center.core_center_le_Z_of_earlier common earlier) le_rfl
  · rw [← common.full_commutation]
    exact commutator_mono (le_sup_left.trans (earlier.factor_inclusions common).2.1) le_rfl

include h in
private theorem original_core_eq : msQ L R = (blockU L).map L.subtype := by
  have hc : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
  rw [msQ,h.sup_eq_top,hc]
  exact h.commutatorCore_eq_internal

include h in
private theorem original_center_eq : sCenter (msQ L R) = (sCenter (blockU L)).map L.subtype := by
  rw [original_core_eq (h := h),centerIn_map _ _ L.subtype_injective]

include h in
private theorem original_fixed_eq : msQ L R ⊓ centralizer (L : Set J) =
    (blockU L ⊓ center L).map L.subtype := by
  rw [map_fixed _ _ L.subtype_injective,range_subtype,original_core_eq (h := h)]

include h in
private theorem original_moved_eq : ⁅sCenter (msQ L R),L⁆ =
    (⁅sCenter (blockU L),(⊤ : Subgroup L)⁆).map L.subtype := by
  rw [map_commutator,← MonoidHom.range_eq_map,range_subtype,original_center_eq (h := h)]

/-- The original center splits into its component-fixed factor and its actual
commutator with L. The latter is the natural module with the CommonFacts marking. -/
theorem center_source_sections
    (hb : 4 < s.geometry.b s.reduction.radical) :
    let Q := msQ L R
    let C := Q ⊓ centralizer (L : Set J)
    let Zc := sCenter Q
    let Uc := ⁅Zc,L⁆
    IsElementaryAbelian 2 Zc ∧ Zc = C ⊔ Uc ∧ C ⊓ Uc = ⊥ ∧
      HasSectionModel L Uc ⊥ (linearThreeActor (h.quotientEquiv.trans common.natural.marking))
        (Representation.specialLinearNatural (k := ZMod 2) 3) := by
  dsimp only
  let r := s.reduction.radical
  let a := alpha r
  let C := core r a
  let Zc := sCenter (blockU L)
  let F := blockU L ⊓ center L
  let Uc := ⁅Zc,(⊤ : Subgroup L)⁆
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hZ := s.intrinsic_center_image
  have hF := s.intrinsic_fixed_image
  have hU := s.intrinsic_moved_image common earlier
  have hsplit : Zc = F ⊔ Uc := by
    apply map_injective s.componentEmbedding_injective
    rw [Subgroup.map_sup,hZ,hF,hU,sup_comm]
    exact Center.core_center_eq_U_sup_fixedFactor common earlier
  have hdisj : F ⊓ Uc = ⊥ := by
    apply map_injective s.componentEmbedding_injective
    rw [map_inf _ _ _ s.componentEmbedding_injective,hF,hU,Subgroup.map_bot]
    exact (Center.U_disjoint_core_fixedFactor common earlier).symm.eq_bot
  have helem : IsElementaryAbelian 2 (sCenter C) := by
    let := Center.core_center_elementary common earlier
    exact IsElementaryAbelian.map C.subtype
  have hZelem : IsElementaryAbelian 2 Zc := by
    let := helem
    let ez := (Zc.equivMapOfInjective s.componentEmbedding
      s.componentEmbedding_injective).trans (MulEquiv.subgroupCongr hZ)
    exact IsElementaryAbelian.of_surjective ez.symm.toMonoidHom ez.symm.surjective
  refine ⟨?_,?_,?_,?_⟩
  · rw [original_center_eq (h := h)]
    let := hZelem
    exact IsElementaryAbelian.map L.subtype
  · rw [original_moved_eq (h := h),original_center_eq (h := h),original_fixed_eq (h := h),
      ← Subgroup.map_sup]
    exact congrArg (map L.subtype) hsplit
  · rw [original_fixed_eq (h := h),original_moved_eq (h := h),← map_inf _ _ _ L.subtype_injective,
      hdisj,Subgroup.map_bot]
  · rw [original_moved_eq (h := h)]
    let eU : Uc ≃* U r a := (Uc.equivMapOfInjective s.componentEmbedding
      s.componentEmbedding_injective).trans (MulEquiv.subgroupCongr hU)
    let eV := ((Uc.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eU).trans
      common.natural.equiv
    have hLU : L ≤ normalizer (Uc.map L.subtype) := by
      have hh := (map_mono (f := L.subtype) (normalizer_commutator_ge_right Zc (⊤ : Subgroup L))).trans
        (Uc.le_normalizer_map L.subtype)
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    have hn : ((⊥ : Subgroup J).subgroupOf (Uc.map L.subtype)).Normal := by
      rw [bot_subgroupOf]; infer_instance
    let := hn
    let e := (QuotientGroup.quotientMulEquivOfEq
      (show (⊥ : Subgroup J).subgroupOf (Uc.map L.subtype) = ⊥ by rw [bot_subgroupOf])).trans
        ((QuotientGroup.quotientBot (G := Uc.map L.subtype)).trans eV)
    refine ⟨bot_le,hLU,by rw [normalizer_eq_top]; exact le_top,hn,?_,?_⟩
    · exact e
    · intro l x y hy
      let ix := (Uc.equivMapOfInjective L.subtype L.subtype_injective).symm x
      let iy := (Uc.equivMapOfInjective L.subtype L.subtype_injective).symm y
      have hix : ((ix : L) : J) = x := congrArg (fun z : Uc.map L.subtype => (z : J))
        ((Uc.equivMapOfInjective L.subtype L.subtype_injective).apply_symm_apply x)
      have hiy : ((iy : L) : J) = y := congrArg (fun z : Uc.map L.subtype => (z : J))
        ((Uc.equivMapOfInjective L.subtype L.subtype_injective).apply_symm_apply y)
      have hxy : (iy : L) = l * (ix : L) * l⁻¹ := Subtype.ext (by
        change ((iy : L) : J) = (l : J) * ((ix : L) : J) * (l : J)⁻¹
        rw [hix,hiy]; exact hy)
      have he := common.natural.action
        (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l)
        (eU ix) (eU iy) (by
          change s.componentEmbedding (iy : L) =
            s.componentEmbedding l * s.componentEmbedding (ix : L) * (s.componentEmbedding l)⁻¹
          rw [hxy,map_mul,map_mul,map_inv])
      have hm : s.source.projection
          (inclusion (show L ≤ s.reduction.overgroup from le_sup_left) l) =
          h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := s.projection_component l
      rw [hm] at he
      exact he

/-- The exact whole fixed-factor equality identifies the literal C_Q(L) with
the source four-group included in the original group. -/
theorem fixed_eq_reducedCentralFour
    (hfixed : core s.reduction.radical (alpha s.reduction.radical) ⊓ centralizer
      (Ltilde s.reduction.radical (alpha s.reduction.radical) : Set (FreeAmalgam s.reduction.radical)) =
        H s.reduction.radical (alpha s.reduction.radical)) :
    msQ L R ⊓ centralizer (L : Set J) = s.reducedCentralFour := by
  have him : (blockU L ⊓ center L).map s.componentEmbedding =
      H s.reduction.radical (alpha s.reduction.radical) := s.intrinsic_fixed_image.trans hfixed
  rw [original_fixed_eq (h := h),reducedCentralFour,← him]
  change ((blockU L ⊓ center L).map L.subtype) =
    (((blockU L ⊓ center L).map
      ((embedM s.reduction.radical).comp
        (inclusion (show L ≤ s.reduction.overgroup from le_sup_left)))).comap (embedM s.reduction.radical)).map s.reduction.overgroup.subtype
  rw [← map_map,comap_map_eq_self_of_injective (embedM_injective _),map_map]
  rfl

include common in
/-- In particular the literal original fixed factor is elementary of order four. -/
theorem fixed_elementary_card_of_fixedFactor
    (hb : 4 < s.geometry.b s.reduction.radical)
    (hfixed : core s.reduction.radical (alpha s.reduction.radical) ⊓ centralizer
      (Ltilde s.reduction.radical (alpha s.reduction.radical) : Set (FreeAmalgam s.reduction.radical)) =
        H s.reduction.radical (alpha s.reduction.radical)) :
    IsElementaryAbelian 2 (msQ L R ⊓ centralizer (L : Set J) : Subgroup J) ∧
      Nat.card (msQ L R ⊓ centralizer (L : Set J) : Subgroup J) = 4 := by
  rw [s.fixed_eq_reducedCentralFour hfixed]
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  exact ⟨s.reducedCentralFour_elementary common earlier,s.reducedCentralFour_card common earlier⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
