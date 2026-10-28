module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionFourMarker
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMarkedControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OddCoreMovement
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentsControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceOutside
public import Theory.GroupTheory.PrimeResidualIntersection

/-!
# An actual outside component in the original quintic marked centralizer

In the order-four partner branch the original marked centralizer escapes
the partner, its faithful two-residual has order five, and its partner
intersection is the centralizer of the original Thompson fixed subgroup.
These proved facts supply the residual intersection, odd-core and
normalizer controls and hence an actual outside C-component.

The conclusion retains the literal marked subgroup and component as
explicit group-theoretic facts. No assertion that the marked centralizer
and the Sylow subgroup generate M is made or used.

Source: Aschbacher--Smith 15.1.18--20, printed pp.1092--1094.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original full quintic source with an order-four partner constructs
one literal outside component with its marked residual and local controls. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_component
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
      Nat.card (localModule T Mc) = 4 →
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
  intro U c d hd s π hp hs hdec hq hfive hcU
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
  have hcard := h.decomposable_five_partner_four_marked_residual_card_five
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hescape : ¬ C ≤ Mc := h.decomposable_five_partner_four_marked_centralizer_not_le
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨hMZ,hTn⟩ := h.decomposable_five_partner_four_marked_centralizer
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hSn := (h.decomposable_five_partner_four_marked_sylow_normal
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).2
  have hpair := h.decomposable_five_maximal_overgroups
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hSylC : Chapter1.IsSylowIn 2 S C := s.local_sylow hM.1.2 h.normalized c d π hs
  have hSylG : Chapter1.IsSylowIn 2 S G1 := h.caseI_centralizer_sylow hG T hM hJ hZ (by
    change Chapter1.IsSylowIn 2 S (G1 ⊓ M)
    rw [inf_comm G1 M]
    exact hSylC)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hNMc : M ⊓ centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact inf_le_right.trans (localModule_centralizer_le_partner T M hu)
  have hI : (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype := by
    let N := M ⊓ centralizer (V : Set G)
    let H := M ⊓ Mc ⊓ G1
    let : (N.subgroupOf C).Normal := caseI_module_centralizer_normal h.normalized
    have hNC : N ≤ C := inf_le_inf_left M (centralizer_le (hZ.trans inf_le_left))
    have hNH : N ≤ H := le_inf (le_inf inf_le_left hNMc) (hNC.trans inf_le_right)
    have hHC : H ≤ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hne : H ≠ C := by
      intro he
      exact hescape (he ▸ (show H ≤ Mc from inf_le_left.trans inf_le_right))
    obtain ⟨P,hP⟩ := hSylC
    apply embedded_pResidual_intersection_of_prime_quotient_residual C N H hNC hNH hHC P
    · intro x hx
      have hxC := map_subtype_le (P : Subgroup C) hx
      have hxS : x ∈ S := hP ▸ hx
      exact ⟨⟨hxC.1,hTMc hxS.1⟩,hxC.2⟩
    · exact hne
    · rw [show Nat.card (pResidual 2 (C ⧸ N.subgroupOf C)) = 5 from hcard]
      decide
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

end CFSG.Quasithin.Chapter15.Section01
