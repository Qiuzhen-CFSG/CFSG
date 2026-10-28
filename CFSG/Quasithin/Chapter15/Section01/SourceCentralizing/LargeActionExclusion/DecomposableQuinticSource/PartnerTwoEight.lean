module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.FullExclusion
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionMarkedFusion
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawCubic
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinary
import all CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SmallModels

/-!
# Exclusion of an order-eight second seed

In the order-two partner branch, an order-eight second seed supplies the
original marked Sylow normality. Prime-residual intersection and pointwise
correction give the marked centralizer, and the original outside-component
catalogue excludes this branch. The local module remains of order two
throughout; no full-partner equality is assumed.
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

/-- Prime-residual marked control when the second seed has order eight. -/
theorem PreparedChosenModule.decomposable_five_partner_two_eight_seed_marked_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      Nat.card (thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc) : Subgroup G) = 8 →
      let E := thompsonFixed T V
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z₁ : Set G)
      let C := M ⊓ G1
      letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
      Nat.card (pResidual 2 (C ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 →
      (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
        (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
          (M ⊓ centralizer (V : Set G)).subtype ∧
      G1 ⊓ Mc = centralizer (E : Set G) ∧
      (T : Subgroup G) ≤ normalizer (G1 ⊓ Mc : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU hE₂eight E Z₁ G1 C hcard
  let S := (T : Subgroup G) ⊓ G1
  let N := M ⊓ centralizer (V : Set G)
  let H := M ⊓ Mc ⊓ G1
  have hNE := h.decomposable_five_fixed_normalizer_eq_partner
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hMcE : Mc ≤ normalizer (E : Set G) := hNE.ge
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSC : S ≤ centralizer (E : Set G) := by
    have hh := ((h.decomposable_five_partner_two_second_seed_marked_sylow
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).2 hE₂eight).1
    exact hh.le.trans inf_le_right
  have hSylC : Chapter1.IsSylowIn 2 S C := s.local_sylow hM.1.2 h.normalized c d π hs
  have hescape : ¬ C ≤ Mc := h.decomposable_five_marked_centralizer_not_le
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hNMc : N ≤ Mc := inf_le_right.trans (h.centralizer_le_partner T hu)
  have hNC : N ≤ C := inf_le_inf_left M
    (centralizer_le (show Z₁ ≤ V from inf_le_right.trans inf_le_left))
  have hNH : N ≤ H := le_inf (le_inf inf_le_left hNMc) (hNC.trans inf_le_right)
  have hHC : H ≤ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hSH : S ≤ H := le_inf (le_inf (inf_le_left.trans hM.1.2)
    (inf_le_left.trans hTMc)) inf_le_right
  have hI : (pResidual 2 H).map H.subtype = (pResidual 2 N).map N.subtype := by
    let : (N.subgroupOf C).Normal := caseI_module_centralizer_normal h.normalized
    obtain ⟨P,hP⟩ := hSylC
    apply embedded_pResidual_intersection_of_prime_quotient_residual C N H hNC hNH hHC P
    · intro x hx
      exact hSH (hP ▸ hx)
    · intro hh
      exact hescape (hh ▸ (show H ≤ Mc from inf_le_left.trans inf_le_right))
    · rw [show Nat.card (pResidual 2 (C ⧸ N.subgroupOf C)) = 5 from hcard]
      decide
  have hHE : H ≤ centralizer (E : Set G) := by
    obtain ⟨P,hP⟩ := hSylC.restrict hSH hHC
    have hgen := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top P)
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hP] at hgen
    rw [←hgen,hI]
    exact sup_le ((map_subtype_le _).trans (inf_le_right.trans
      (centralizer_le (show E ≤ V from inf_le_left)))) hSC
  have hMZ : G1 ⊓ Mc = centralizer (E : Set G) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨n,hn,hnE,hnact⟩ := h.marked_normalizer_pointwise_correction hG T hM hJ
        (show E ≤ V from inf_le_left) (show Z₁ ≤ V from inf_le_right.trans inf_le_left)
        g hg.1 (hMcE hg.2)
      have hnC : n ∈ centralizer (E : Set G) := hHE ⟨⟨hn.1,hNE.le hnE⟩,hn.2⟩
      intro e he
      have hh : g*e*g⁻¹ = e := by
        rw [←hnact e he,←hnC e he,mul_inv_cancel_right]
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · exact le_inf (centralizer_le (show Z₁ ≤ E from inf_le_right))
        ((Subgroup.centralizer_le_normalizer (E : Set G)).trans hNE.le)
  refine ⟨hI,hMZ,?_⟩
  change (T : Subgroup G) ≤ normalizer ((G1 ⊓ Mc : Subgroup G) : Set G)
  rw [hMZ]
  exact (hTMc.trans hMcE).trans (normalizer_le_normalizer_centralizer _)


/-- The order-eight second seed constructs
one literal outside component with its marked residual and local controls. -/
theorem PreparedChosenModule.decomposable_five_partner_two_eight_seed_raw_component
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
      Nat.card (thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc) : Subgroup G) = 8 →
      (let Z := thompsonPlane T V (c.ambientFactor d s.first).space
       let C := M ⊓ centralizer (Z : Set G)
       letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
       Nat.card (pResidual 2 (C ⧸
         (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
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
        Z1 ≤ thompsonFixed T V ∧ Nat.card Z1 = 4 ∧
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 ∧
        MZ = centralizer (thompsonFixed T V : Set G) ∧
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
        (IsComponent G1 (L.subgroupOf G1) ∨ generalizedFitting L = pCore 2 L) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU hE₂eight hcard
  let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
  let G1 := centralizer (Z1 : Set G)
  let MZ := G1 ⊓ Mc
  let Q1 := MZ.pCoreIn 2
  let S := (T : Subgroup G) ⊓ G1
  let C := M ⊓ G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let Y := (pResidual 2 MZ).map MZ.subtype
  have hZ : Z1 ≤ thompsonFixed T V := inf_le_right
  have hZcard : Nat.card Z1 = 4 := s.thompson_card s.first
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by rw [hZcard]; decide)
  have hescape : ¬ C ≤ Mc := h.decomposable_five_marked_centralizer_not_le
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨hI,hMZ,hTn⟩ := h.decomposable_five_partner_two_eight_seed_marked_control
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive hcU hE₂eight hcard
  have hSn := ((h.decomposable_five_partner_two_second_seed_marked_sylow
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).2 hE₂eight).2
  have hpair := h.decomposable_five_maximal_overgroups
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hSylC : Chapter1.IsSylowIn 2 S C := s.local_sylow hM.1.2 h.normalized c d π hs
  have hSylG : Chapter1.IsSylowIn 2 S G1 := h.caseI_centralizer_sylow hG T hM hJ hZ (by
    change Chapter1.IsSylowIn 2 S (G1 ⊓ M)
    rw [inf_comm G1 M]
    exact hSylC)
  have hrank : primeRank 2 (internalActionImage M V h.normalized) ≤ 2 := by
    subst V
    exact source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
      (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hrank)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  have hseed : centralInvolutions T ⊓ V ≤ Z1 ⊔ W :=
    (s.full_residual_bounds hM.1.2 h.normalized c d hJi).2.2
  have hmove : W ≤ V ∧ ⁅W,R⁆ = W := marked_residual_movement h.normalized Z1
  have hplus : centralInvolutions T ⊓ (Z1 ⊔ W) ≠ ⊥ := by
    have hseedne : centralInvolutions T ⊓ V ≠ ⊥ := by
      intro hz
      apply h.nontrivial
      rw [h.seed_span,hz]
      exact bot_unique (conjugateSpanBy_le bot_le (by
        change M ≤ normalizer (⊥ : Subgroup G)
        rw [normalizer_eq_top]
        exact le_top))
    intro he
    exact hseedne (bot_unique ((le_inf inf_le_left hseed).trans_eq he))
  obtain ⟨P,hP⟩ := hSylG
  have hZelem : IsElementaryAbelian 2 Z1 := IsElementaryAbelian.of_le (hZ.trans inf_le_left)
  have h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z := by
    intro z hz hzne
    exact CaseIMarkedSubgroup.central_involution_hypotheses hG hu hZne hZelem P
      (hP.le.trans inf_le_left) hz hzne
  have ho := h.caseI_oddCore_eq_bot hG Z1 W hZ hmove.1 P hmove.2 hplus h115
  obtain ⟨hcontrol,hn⟩ := h.marked_core_normalizer_control_of_pair
    hG T hempty hM hmany hJ hu hpair hZ hZne hTn
  have hQne : Q1 ≠ ⊥ := CaseIMarkedSubgroup.core_nontrivial hZ hZne hM hu h
  have hresN := h.marked_residual_normalizer_control_of_pair
    hG T hempty hM hmany hJ hu hpair hZ hZne hTn ⟨P,hP⟩
  obtain ⟨L,hLG1,hLc,hquasi,hout⟩ := source_caseI_15_1_19_6_of_global_control
    hG M Mc Z1 hZne (by let := hZelem; exact IsElementaryAbelian.isPGroup 2 Z1)
    hQne hcontrol hn ho (fun hh => hescape (hh.trans inf_le_right))
    (inf_le_inf_left _ hresN)
  have hWG1 : W ≤ G1 := hmove.1.trans
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left)))
  have hmovement := source_caseI_component_movement hG T M Mc Z1 W L P
    hWG1 hmove.2 hplus h115 ⟨hLG1,hLc⟩ hout
  have hG1H : G1 ∈ Chapter1.H G := by
    obtain ⟨z,hz,hzne⟩ := (centralInvolutions T ⊓ (Z1 ⊔ W)).bot_or_exists_ne_one.resolve_left hplus
    exact (h115 z hz.1 hzne).mem_H
  have hloc := ComponentModels.source20_mem_L_of_cComponent hG1H ⟨P,hP⟩ hLG1 hLc
  have hLout : ¬ L ≤ M := by
    intro hLM
    let : Group.IsPerfect (L.subgroupOf G1) := hLc.perfect
    let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hLG1).toMonoidHom) (subgroupOfEquivOfLe hLG1).surjective
    exact hout (le_inf hLG1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hLM).trans
        (localModule_centralizer_le_partner T M hu)))
  have hTQ : (T : Subgroup G) ≤ normalizer (Q1 : Set G) :=
    hTn.trans (normalizer_le_normalizer_characteristic_image MZ (pCore 2 MZ))
  have hZE : centralInvolutions T ≤ thompsonFixed T V := by
    refine le_inf ?_ ?_
    · rw [hfull]
      exact le_conjugateSpanBy _ _
    · exact (centralInvolutions_le_centralizer_sylow T).trans
        (centralizer_le (ChapterB.thompsonJ_le _ _))
  have hYseed : Y ≤ centralizer (centralInvolutions T : Set G) :=
    (map_subtype_le _).trans (hMZ.le.trans (centralizer_le hZE))
  have halt : IsComponent G1 (L.subgroupOf G1) ∨ generalizedFitting L = pCore 2 L := by
    rcases hLc.component_or_generalizedFitting_eq_pCore ho with ho | hf
    · exact Or.inl ho
    · let e := subgroupOfEquivOfLe hLG1
      exact Or.inr ((map_generalizedFitting_equiv e).symm.trans
        ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e)))
  exact ⟨L,hZ,hZcard,hcard,hMZ,ho,⟨P,hP⟩,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,⟨P,hP,h115⟩,⟨hLG1,hLc⟩,hout,hquasi,hloc,
    ComponentModels.source20_sylow_intersection hloc,hLout,hmovement.1,hmovement.2,halt⟩


/-- An order-eight second seed is impossible in the literal order-two partner source. -/
theorem PreparedChosenModule.decomposable_five_partner_two_eight_seed_false
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
      Nat.card (thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc) : Subgroup G) = 8 →
      (let Z := thompsonPlane T V (c.ambientFactor d s.first).space
       let C := M ⊓ centralizer (Z : Set G)
       letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
       Nat.card (pResidual 2 (C ⧸
         (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) → False := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hE₂eight hcard
  obtain ⟨L,hZ,hZcard,_hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,hcases⟩ :=
    h.decomposable_five_partner_two_eight_seed_raw_component hG T hempty hM hmany hJ hu hne hfull
      c d hd s π hp hs hdec hratio hfive hcU hE₂eight hcard
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
  have hres := quintic_quotient_cubic_residual h.normalized hLc.1 hcard
  have hfit : generalizedFitting L = pCore 2 L := by
    rcases hcases with hordinary | hfit
    · obtain ⟨hcenter,_⟩ := raw_ordinary_center hLc.1 hordinary ho
      have h115copy := h115
      obtain ⟨P,_,hi⟩ := h115copy
      obtain ⟨hnZ,hfaith,hmodels⟩ := raw_ordinary_marked_actions hG T hLc.1 hout P hi hordinary
      apply False.elim
      apply h.decomposable_five_raw_not_ordinary hG T hempty hM hmany hJ hu hfull
        c d hd s π hp hs hdec hratio hfive hLc.1 hordinary hcenter hquasi hSyl hnL hmove
        hnZ hfaith hSylG h115 hout houtM hcontrol hresN hn hI
      intro z hz hzne
      obtain ⟨α,_,hm⟩ := (hmodels z hz hzne).2
      exact ⟨α,hm⟩
    · exact hfit
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

/-- Under the original prime-five residual hypothesis, the literal second
seed in the order-two partner branch has order four. -/
theorem PreparedChosenModule.decomposable_five_partner_two_second_seed_card_four
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
      Nat.card (thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc) : Subgroup G) = 4 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hcard
  have hcases := (h.decomposable_five_partner_two_second_seed
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU).2.2.1
  rcases hcases with hfour | height
  · exact hfour
  · exact (h.decomposable_five_partner_two_eight_seed_false
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hratio hfive
        hcU height hcard).elim

end CFSG.Quasithin.Chapter15.Section01
