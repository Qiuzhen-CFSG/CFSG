module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineOrdinaryHigherField
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineAlternating
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePreExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.OrdinaryComplete

/-!
# The original Nine ordinary catalogue without global residual centralization

The actual marked residual supplies the Borel and small-model exclusions.
Applying the exhaustive marked involution models yields the initial ordinary
catalogue; the independent local-family nonblock theorem excludes its
exceptional higher-field remainder. The same actual exchanged source then
excludes ordinary component status.

The original full Nine module and marker are retained. No global residual,
ordinary catalogue, or component model is assumed in the actual consumer.
Source: Aschbacher--Smith 15.1.20--22, printed pp.1094--1100.
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

/-- The actual full Nine row gives the original ordinary catalogue on the
same component, using local marked residual control throughout. -/
theorem PreExclusionSource.nine_ordinary20_of_local_source
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : d.Ordinary20Alternatives := by
  have hpair := h.nine_maximal_overgroups hG T hempty hM hJ hu h9
  have hbound := h.marked_residual_normalizer_control_of_pair hG T hempty hM hmany hJ hu
    hpair d.Z1_le_fixed d.Z1_ne_bot s.sylow_normalizes_MZ s.centralizer_sylow
  have hMcC := (h.nine_partner_centralizer hG T hempty hM hJ hu hne hfull h9).1.le
  have hpsl (e : d.L ≃* Matrix.PSL3Two.PSL) : False :=
    s.nine_false_of_pslThreeTwo_equiv (h := h) hG hempty hM hu hmany hJ hne hfull h9 hL e
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

/-- The same Nine exchanged source cannot have ordinary component status. -/
theorem ExchangedSource.nine_not_ordinary
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hp : p = 3 ∨ p = 5) : ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  exact e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.nine_ordinary20_of_local_source (h := h)
      hG hempty hM hJ hu hne hmany hfull h9 hL)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
