module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawConstrainedSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherLinearNormalizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherSymplecticNormalizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherG2
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawRankOneImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerSmallExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSevenExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawBinaryParabolicSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicExclusion
import all CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SmallModels

/-! The complete normalizer B5 catalogue is excluded on the single L
selected by the original order-four partner source. Every model is consumed
using its actual quotient/action producer. No M-generation field, residual
prior, new classifier premise or abstract-star identification is required. -/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open ChapterC ChapterC.C27Source
open ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original quintic source has no order-four partner module: one
actual selected component contradicts its complete normalizer catalogue. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
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
      Nat.card (localModule T Mc) = 4 → False := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU
  obtain ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,
    hres,hneq,hnot2,hnot5,hfit,hi,_,_,_⟩ :=
    h.decomposable_five_partner_four_raw_constrained hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hratio hfive hcU
  let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let I := (L.subgroupOf H).map q
  have hZne : Z1 ≠ ⊥ := by
    intro he
    change Nat.card Z1 = 4 at hZcard
    rw [he,card_bot] at hZcard
    omega
  have hlocal : L ∈ Chapter1.LIn (centralizer (Z1 : Set G)) S := ⟨hLc.1,hloc⟩
  obtain ⟨hr,_,_,_,_,hIJ,⟨source⟩⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hlocal hquasi hfit hout houtM
  let := hr.elementary
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := offenderSubgroup ρ
  have model : StarModels.Model I := StarModels.model_of_source _ (subgroupOfEquivOfLe hIJ).symm source
  have noTwo (F : Type) [Field F] [Finite F] [CharP F 2] : IsEmpty (I ≃* SL(2,F)) :=
    h.raw_component_normalizer_not_rankOne hG T hM hJ hu hZ hZne hSylG hLc hloc
      hquasi hfit hout houtM hcontrol hresN hI hnL hmove F
  have noSix (e : (I ⧸ center I) ≃* alternatingGroup (Fin 6)) : False :=
    h.raw_not_six_normalizer_image hG T hM hJ hu hfull hZ hZne hSylG hlocal houtM hi hres e
  have noBinary {n : ℕ} (hn : n=4 ∨ n=5) (e : I ≃* SL(n,ZMod 2)) : False :=
    h.raw_not_binary_linear_normalizer_image hG T hempty hM hJ hu hfull hZ hZne
      hSylG hlocal hquasi hfit hout hres hn e
  cases model with
  | linearTwo F e => exact (noTwo F.Carrier).false e
  | linearThree F e =>
    by_cases hF : F.degree=1
    · let : Fintype F.Carrier := Fintype.ofFinite _
      let f : F.Carrier ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        rw [←Nat.card_eq_fintype_card,F.card_eq,hF]
        simp)
      exact (h.decomposable_five_raw_not_normalizer_binaryThree hG T hempty hM hmany hJ hu
        hfull c d hd s π hp hs hdec hratio hfive hnL hmove hZ hZne hloc hSylG hQne hTn hi).false
          (e.trans (Atlas.fieldEquivSL 3 f))
    · have hlarge : 1 < F.degree := by have := F.degree_pos; omega
      exact h.raw_component_normalizer_not_higher_linear hG T hempty hM hJ hu
        hZ hZne hlocal hi F hlarge e
  | symplectic F hn e =>
    exact h.raw_component_normalizer_not_higher_symplectic hG T hempty hM hJ hu
      hZ hZne hlocal houtM hi F.card_eq hn e
  | g2 F hn e =>
    exact h.raw_component_normalizer_not_higherG2 hG T hempty hM hJ hu
      hZ hZne hlocal hquasi hfit hout hn ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨e⟩⟩
  | g2DerivedTwo e =>
    exact (h.decomposable_five_raw_not_normalizer_g2 hG T hempty hM hmany hJ hu
      hfull c d hd s π hp hs hdec hratio hfive hnL hmove hZ hZne hloc hSylG hi).false e
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact (noTwo BinaryField.four.Carrier).false (e.trans SmallModels.alternatingFiveLinearEquiv)
    · exact noSix ((QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
        ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
          QuotientGroup.quotientBot))
    · obtain ⟨hBL,_,hBcard⟩ := h.decomposable_five_raw_moving_support_action
        hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hratio hfive hnL hmove
      exact (h.raw_seven_normalizer_image_false hG T hM hJ hu hZ hZne hlocal houtM
        hSylG hi hres (plane_le _) hBL hBcard).false e
    · exact noBinary (Or.inl rfl) (e.trans SmallModels.alternatingEightLinearEquiv)
  | linearFiveTwo e => exact noBinary (Or.inr rfl) e
  | tripleSix _ e => exact noSix e

end CFSG.Quasithin.Chapter15.Section01
