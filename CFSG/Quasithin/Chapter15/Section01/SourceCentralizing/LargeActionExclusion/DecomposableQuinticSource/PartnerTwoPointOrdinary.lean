module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoPointComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.FullExclusion
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawCubic
import all CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SmallModels

/-!
# The chosen point component is ordinary

The complete constrained normalizer catalogue is applied at the literal
point centralizer. Only the quintic movement inputs are transported through
the proved equality of embedded residuals; the point, Sylow, component,
normalizers, and quotient denominators remain unchanged.
-/

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

/-- The actual point component is ordinary: every constrained alternative
is excluded using the original quintic residual and its genuine support. -/
theorem PreparedChosenModule.decomposable_five_partner_two_point_ordinary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      Nat.card (localModule T Mc) = 2 →
      (let Z := thompsonPlane T V (c.ambientFactor d s.first).space
       let C := M ⊓ centralizer (Z : Set G)
       letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
       Nat.card (pResidual 2 (C ⧸
         (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) →
      let E₂ := thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc)
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      ∃ a ∈ Z₁, ∃ b ∈ Z₂, a ≠ 1 ∧ b ≠ 1 ∧
        localModule T Mc = zpowers (a*b) ∧ E₂ = zpowers a ⊔ zpowers b ∧
      let Z1 := zpowers a
      let G1 := centralizer (Z1 : Set G)
      let MZ := G1 ⊓ Mc
      let Q1 := MZ.pCoreIn 2
      let S := (T : Subgroup G) ⊓ G1
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let W := ⁅V,R⁆
      let Y := (pResidual 2 MZ).map MZ.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      ∃ L : Subgroup G,
        Z1 ≤ thompsonFixed T V ∧ Nat.card Z1 = 2 ∧
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 ∧
        MZ = centralizer (E₂ : Set G) ∧
        pPrimeCore 2 G1 = ⊥ ∧ Chapter1.IsSylowIn 2 S G1 ∧
        (S.subgroupOf (T : Subgroup G)).Normal ∧
        (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
          (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
            (M ⊓ centralizer (V : Set G)).subtype ∧
        centralInvolutions T ⊓ V ≤ Z1 ⊔ W ∧
        Q1 ≠ ⊥ ∧ Q1.characteristicNormalizerClosure ≤ Mc ∧
        G1 ⊓ normalizer (Q1 : Set G) = MZ ∧
        (T : Subgroup G) ≤ normalizer (MZ : Set G) ∧
        (T : Subgroup G) ≤ normalizer (Q1 : Set G) ∧
        normalizer (Y : Set G) ≤ Mc ∧ Y ≤ centralizer (centralInvolutions T : Set G) ∧
        (∃ P : Sylow 2 G1, (P : Subgroup G1).map G1.subtype = S ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z) ∧
        L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ MZ ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ W ≤ normalizer (L : Set G) ∧ ⁅L,W⁆ ≠ ⊥ ∧
        IsComponent G1 (L.subgroupOf G1) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hcard E₂ Z₁ Z₂
  obtain ⟨a,ha,b,hb,hane,hbne,hU,hE,L,hZ,hZcard,hc,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
      hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,hcases⟩ :=
    h.decomposable_five_partner_two_point_component
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hratio hfive hcU hcard
  let Z1 := zpowers a
  let G1 := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ G1
  let R₀ := (pResidual 2 (M ⊓ G1 : Subgroup G)).map (M ⊓ G1).subtype
  let Rorig := (pResidual 2 (M ⊓ centralizer (Z₁ : Set G) : Subgroup G)).map
    (M ⊓ centralizer (Z₁ : Set G)).subtype
  have hReq : R₀ = Rorig := by
    have hC : M ⊓ G1 = M ⊓ centralizer ({a} : Set G) := by
      simp only [G1, Z1, zpowers_eq_closure, centralizer_closure]
    exact (congrArg (fun K : Subgroup G => (pResidual 2 K).map K.subtype) hC).trans
      (s.quintic_point_residual_eq_marked h.normalized c d π hp hs hfive a ha hane)
  have hnOrig : Rorig ⊔ ⁅V,Rorig⁆ ≤ normalizer (L : Set G) := by
    rw [← hReq]
    exact hnL
  have hmOrig : ⁅L,⁅V,Rorig⁆⁆ ≠ ⊥ := by
    rw [← hReq]
    exact hmove
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by
    change Nat.card Z1 = 2 at hZcard
    rw [hZcard]
    decide)
  have hres := quintic_quotient_cubic_residual h.normalized hLc.1 hc
  have hord : IsComponent G1 (L.subgroupOf G1) := by
    rcases hcases with hord | hfit
    · exact hord
    · exfalso
      let R := S ⊓ normalizer (L : Set G)
      let H := L ⊔ R
      let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
      let C := centralizer (W : Set H)
      let q := QuotientGroup.mk' C
      let I := (L.subgroupOf H).map q
      have hnot2 := h.raw_component_not_linear_two hG T hM hJ hu
        hZ hZne hSylG hLc hloc hquasi hout houtM hcontrol hresN hI hmove
      have hnot5 := h.raw_component_not_alternating_five hG T hM hJ hu
        hZ ⟨hLc.1,hloc⟩ hquasi hout houtM hSylG hnL hmove
      have hG1 := caseI_centralizer_sqtk hG Z1 hZne
        ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
      obtain hrank | ⟨hi,_⟩ := raw_constrained_component_rankOne_or_star
        (centralizer (Z1 : Set G)) Mc L hG1 ho hQne hcontrol hn hLc hquasi hfit hout
      · exact (hrank.elim hnot2 hnot5).elim
      · have hlocal : L ∈ Chapter1.LIn (centralizer (Z1 : Set G)) S := ⟨hLc.1,hloc⟩
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
            have hb := h.raw_normalizer_binaryThree_block hG T hempty hM hJ hu hZ hZne
              hloc hSylG hQne hTn hi (e.trans (Atlas.fieldEquivSL 3 f))
            obtain ⟨Y,hY,hYn,hYc⟩ := h.decomposable_five_raw_noncentral_actor
              hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hratio hfive hnOrig hmOrig
            exact hYc (hb.quintic_centralizes hY hYn)
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
          have hb := h.raw_normalizer_g2_block hG T hempty hM hJ hu hZ hZne hloc hSylG hi e
          exact h.decomposable_five_raw_not_g2_block hG T hempty hM hmany hJ hfull
            c d hd s π hp hs hdec hratio hfive hnOrig hmOrig hb
        | alternating n hn e =>
          rcases hn with rfl | rfl | rfl | rfl
          · exact (noTwo BinaryField.four.Carrier).false (e.trans SmallModels.alternatingFiveLinearEquiv)
          · exact noSix ((QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
              ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
                QuotientGroup.quotientBot))
          · obtain ⟨hBL,_,hBcard⟩ := h.decomposable_five_raw_moving_support_action
              hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hratio hfive hnOrig hmOrig
            exact (h.raw_seven_normalizer_image_false hG T hM hJ hu hZ hZne hlocal houtM
              hSylG hi hres (plane_le _) hBL hBcard).false e
          · exact noBinary (Or.inl rfl) (e.trans SmallModels.alternatingEightLinearEquiv)
        | linearFiveTwo e => exact noBinary (Or.inr rfl) e
        | tripleSix _ e => exact noSix e
  exact ⟨a,ha,b,hb,hane,hbne,hU,hE,L,hZ,hZcard,hc,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,hord⟩

end CFSG.Quasithin.Chapter15.Section01
