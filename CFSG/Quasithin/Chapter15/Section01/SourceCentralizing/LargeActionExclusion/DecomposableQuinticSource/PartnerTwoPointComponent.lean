module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoPointControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OddCoreMovement
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentsControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceOutside

/-!
# An actual component in the chosen point centralizer

The order-four second seed supplies the genuine line Z=<a>, distinct from
both the original marked plane and the central diagonal Uc. Its residual
is the original marked residual. The point centralizer therefore has the
same moving support and yields an actual outside component with all local
controls on that literal line.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The surviving original source supplies a literal outside component at
an actual support point of E₂, with its original residual and denominator. -/
theorem PreparedChosenModule.decomposable_five_partner_two_point_component
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
        (IsComponent G1 (L.subgroupOf G1) ∨ generalizedFitting L = pCore 2 L) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hcard E₂ Z₁ Z₂
  obtain ⟨a, ha, b, hb, hane, hbne, hU, hE, hc, hSylC, hSylG, hSn, hMZ, hTn, hI⟩ :=
    h.decomposable_five_partner_two_point_control
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hratio hfive hcU hcard
  let Z1 := zpowers a
  let G1 := centralizer (Z1 : Set G)
  let MZ := G1 ⊓ Mc
  let Q1 := MZ.pCoreIn 2
  let S := (T : Subgroup G) ⊓ G1
  let C := M ⊓ G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let Y := (pResidual 2 MZ).map MZ.subtype
  have hZ : Z1 ≤ thompsonFixed T V := zpowers_le.mpr ha.2
  have hZcard : Nat.card Z1 = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha.2.1) hane
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by rw [hZcard]; decide)
  have hescape : ¬ C ≤ Mc := by
    intro hh
    apply h.decomposable_five_marked_centralizer_not_le
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive
    exact (inf_le_inf_left M (centralizer_le (zpowers_le.mpr ha))).trans hh
  have hpair := h.decomposable_five_maximal_overgroups
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive
  have hrank : primeRank 2 (internalActionImage M V h.normalized) ≤ 2 := by
    subst V
    exact source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
      (Or.inr (Or.inr (Or.inl hdec)))
  have hactors := (h.thompson_actors T hM.1.2 hratio
    (fun A hA => hA.rank_le_of_primeRank_le hrank)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm hactors c d π hp hdec).1
  have hReq : R = (pResidual 2 (M ⊓ centralizer (Z₁ : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z₁ : Set G)).subtype := by
    have hC : C = M ⊓ centralizer ({a} : Set G) := by
      simp only [C, G1, Z1, zpowers_eq_closure, centralizer_closure]
    exact (congrArg (fun K : Subgroup G => (pResidual 2 K).map K.subtype) hC).trans
      (s.quintic_point_residual_eq_marked h.normalized c d π hp hs hfive a ha hane)
  have hBW : plane V (c.ambientFactor d s.second).space ≤ W := by
    rw [show W = ⁅V, R⁆ from rfl, hReq]
    exact (s.full_residual_bounds hM.1.2 h.normalized c d hJi).2.1
  have hUZ := (h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU).1
  have hseed : centralInvolutions T ⊓ V ≤ Z1 ⊔ W := by
    apply inf_le_left.trans
    rw [← hUZ, hU]
    exact zpowers_le.mpr (mul_mem_sup (mem_zpowers a) (hBW hb.1))
  have hmove : W ≤ V ∧ ⁅W,R⁆ = W := marked_residual_movement h.normalized Z1
  have hplus : centralInvolutions T ⊓ (Z1 ⊔ W) ≠ ⊥ := by
    intro he
    have huIn : a*b ∈ centralInvolutions T ⊓ (Z1 ⊔ W) := by
      refine ⟨?_, mul_mem_sup (mem_zpowers a) (hBW hb.1)⟩
      rw [← hUZ, hU]
      exact mem_zpowers (a*b)
    have hab1 : a*b = 1 := mem_bot.mp (he ▸ huIn)
    have haB : a ∈ Z₂ := by
      rw [eq_inv_of_mul_eq_one_left hab1]
      exact Z₂.inv_mem hb
    exact hane (mem_bot.mp (s.thompson_disjoint ▸ (show a ∈ Z₁ ⊓ Z₂ from ⟨ha, haB⟩)))
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
  have hYseed : Y ≤ centralizer (centralInvolutions T : Set G) := by
    have hMcZ := (h.decomposable_five_partner_two_fixed_line
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU).2.1
    exact ((map_subtype_le _).trans inf_le_right).trans_eq hMcZ
  have halt : IsComponent G1 (L.subgroupOf G1) ∨ generalizedFitting L = pCore 2 L := by
    rcases hLc.component_or_generalizedFitting_eq_pCore ho with ho | hf
    · exact Or.inl ho
    · let e := subgroupOfEquivOfLe hLG1
      exact Or.inr ((map_generalizedFitting_equiv e).symm.trans
        ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e)))
  exact ⟨a,ha,b,hb,hane,hbne,hU,hE,L,hZ,hZcard,hc,hMZ,ho,⟨P,hP⟩,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,⟨P,hP,h115⟩,⟨hLG1,hLc⟩,hout,hquasi,hloc,
    ComponentModels.source20_sylow_intersection hloc,hLout,hmovement.1,hmovement.2,halt⟩

end CFSG.Quasithin.Chapter15.Section01
