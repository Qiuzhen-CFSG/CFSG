module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableOrdinaryLinear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineOrdinaryInitial
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableComponents

/-!
# Ordinary component exclusion from the original marked local controls

The ordinary marked-model catalogue uses the central-seed centralizer and
the normalizer bound on the actual marked residual. These inputs are
supplied independently in both the Nine and cubic decomposable rows.
The same component and all its marked actions are preserved; no global
Thompson residual conclusion is used. This covers both four-element and
sixteen-element exchanged supports.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Chapter1.Section02.LocalModels Chapter15.Section03.Candidates.ComponentStructure
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original local residual bound and central-seed centralizer give
the ordinary catalogue on the same marked component. -/
theorem PreExclusionSource.ordinary20_of_local_control
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hMcC : Mc ≤ centralizer (centralInvolutions T : Set G))
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : d.Ordinary20Alternatives := by
  have hpsl (e : d.L ≃* Matrix.PSL3Two.PSL) : False :=
    s.false_of_pslThreeTwo_equiv_of_local_control (h := h) hG hM hMcC hbound hL e
  have hrankTwo (hm : RankTwoTheoremC d.L) :
      d.Ordinary20Alternatives ∨ d.OrdinaryExceptionalHigherField := by
    cases hm with
    | linear n hn hm =>
        by_cases hn1 : n = 1
        · subst n
          obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
          let := Fintype.ofFinite F
          let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
            simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hF)
          exact (hpsl
            (e.trans (Atlas.fieldEquivPSL 3 k))).elim
        · exact False.elim (s.false_of_initial_higherField_of_local_residual (h := h) hG hempty hM hJ hu hbound hL
            (.inl ⟨n,by omega,.inl hm⟩))
    | symplectic n hn hm =>
        exact False.elim (s.false_of_initial_higherField_of_local_residual (h := h) hG hempty hM hJ hu hbound hL
          (.inl ⟨n,by omega,.inr hm⟩))
    | g2 n hn hm => exact .inr (.g2 n (by omega) hm)
    | triality n hn hm =>
        by_cases hn1 : n = 1
        · subst n
          obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff d.L).mp
            (by simpa only [pow_one] using hm)
          exact .inl (s.ordinary20_of_triality (h := h) hG hM hu hL e)
        · exact .inr (.triality n (by omega) hm)
    | ree m hm model => exact .inr (.ree m hm model)
    | symplectic_derived hm =>
        obtain ⟨e⟩ := hm
        exact (s.false_of_alternatingSix_equiv_local (h := h) hG hMcC hbound hL
          (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
    | g2_derived hm =>
        exact .inl (s.ordinary20_of_binaryG2Derived (h := h) hG hM hu hL (Classical.choice hm))
    | tits hm => exact .inl (s.ordinary20_of_tits (h := h) hG hM hu hL (Classical.choice hm))
  have hmarked {α : MulAut d.L} (hm : ModelAction115 d.L α) :
      d.Ordinary20Alternatives ∨ d.OrdinaryExceptionalHigherField := by
    cases hm with
    | lie _ hm _ =>
        rcases hm with hm | hm | ⟨n,hn,hm⟩
        · exact .inl (s.ordinary20_of_rankOne_of_local_residual (h := h) hG hM hu hbound hL (.inl hm))
        · exact hrankTwo hm
        · exact .inl (s.ordinary20_of_binaryPSL (h := h) hG hM hu hL hn hm)
    | two_cover hc _ hm _ =>
        rcases hm with hm | hm
        · exact (s.false_of_initial_higherField_of_local_residual (h := h) hG hempty hM hJ hu hbound hL (.inr hm)).elim
        · exact .inr (.g2_cover hc hm)
    | six σ _ ha =>
        exact (s.false_of_alternating_action_local (h := h) hG hu hMcC hbound hL
          (Or.inl rfl) ha).elim
    | seven σ _ ha =>
        exact (s.false_of_alternating_action_local (h := h) hG hu hMcC hbound hL
          (Or.inr rfl) ha).elim
    | odd hm _ =>
        rcases s.ordinary_odd_binary_models (h := h) hM.1.2 hL hm with he | he
        · obtain ⟨e⟩ := he
          exact .inl (s.ordinary20_of_rankOne_of_local_residual (h := h) hG hM hu hbound hL
            (.inl (.linear 2 (by decide) ⟨GaloisField 2 2,inferInstance,inferInstance,
              GaloisField.card 2 2 (by decide),⟨e⟩⟩)))
        · obtain ⟨e⟩ := he
          exact (hpsl e).elim
    | sporadic name hn hm _ =>
        exact .inl (s.ordinary20_of_sporadic_quotient (h := h) hG hempty hM hJ hu hL name hn hm)
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,_,hm⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  exact (hmarked hm).resolve_right
    (s.not_exceptional_of_nonblock_containment (h := h) hG hempty hM hJ hu hL
      (d.source_rankOneNonblockContainment hG hempty hM hJ hu h))

/-- The original exchanged source cannot have ordinary component status
under the independently supplied marked local controls. -/
theorem ExchangedSource.not_ordinary_of_local_control
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hMcC : Mc ≤ centralizer (centralInvolutions T : Set G))
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hp : p = 3 ∨ p = 5) : ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  exact e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.ordinary20_of_local_control (h := h)
      hG hempty hM hJ hu hMcC hbound hL)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original cubic decomposable source constructs its actual constrained
component, with both sixteen-element supports and its local residual control.
Ordinary component status is excluded without global15.1.14. -/
theorem PreparedChosenModule.decomposable_three_constrained_without_residual
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
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 3 →
      ∃ e : CaseIComponentData T M Mc V,
        e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space ∧
        e.row = .six ∧ Nat.card e.Z1 = 4 ∧
        e.PreExclusionSource h.normalized 3 ∧ e.ExchangedPlaneGeometry ∧
        e.ExchangedSource ∧
        generalizedFitting e.L = pCore 2 e.L ∧
        normalizer ((pResidual 2 e.MZ).map e.MZ.subtype : Set G) ≤ Mc := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hthree
  obtain ⟨e,heZ,herow,hecard,hepre,heplanes,hex,hNY⟩ :=
    h.decomposable_three_exchanged_without_residual
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hthree
  have hMcC := (h.decomposable_three_partner_centralizer
    hG T hempty hM hJ hu hne hfull c d s π hp hs hdec hthree).1.le
  have hnot := hex.not_ordinary_of_local_control (h := h) hepre
    hG hempty hM hJ hu hMcC hNY (Or.inl rfl)
  have hf := (e.L_component.2.component_or_generalizedFitting_eq_pCore hepre.odd_core).resolve_left hnot
  have hfL : generalizedFitting e.L = pCore 2 e.L := by
    let j : e.L.subgroupOf e.G1 ≃* e.L := subgroupOfEquivOfLe e.L_component.1
    exact (map_generalizedFitting_equiv j).symm.trans
      ((congrArg (Subgroup.map j.toMonoidHom) hf).trans (pCore_map_iso 2 j))
  exact ⟨e,heZ,herow,hecard,hepre,heplanes,hex,hfL,hNY⟩

end CFSG.Quasithin.Chapter15.Section01
