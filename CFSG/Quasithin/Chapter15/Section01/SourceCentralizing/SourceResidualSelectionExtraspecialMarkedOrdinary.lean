module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedOrdinaryAlternating
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableOrdinary
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.ResidualExclusion

/-!
# Ordinary exclusion for the same extraspecial marker without global residual control

The literal residual of M_Z centralizes the original seed and has its full
normalizer in Mc. These two local facts give the ordinary catalogue on the
same component. Its post-rank-one quotient contradicts the original
extraspecial marker's central-cubic movement. No global 15.1.14 conclusion,
whole-partner seed centralization or catalogue callback is assumed.
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
theorem PreExclusionSource.ordinary20_of_marked_residual_seed
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hYseed : (pResidual 2 d.MZ).map d.MZ.subtype ≤
      centralizer (centralInvolutions T : Set G))
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : d.Ordinary20Alternatives := by
  have hpsl (e : d.L ≃* Matrix.PSL3Two.PSL) : False :=
    s.false_of_pslThreeTwo_equiv_of_residual_seed (h := h) hG hM hYseed hbound hL e
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
        exact (s.false_of_alternatingSix_equiv_of_residual_seed (h := h) hG hYseed hbound hL
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
        exact (s.false_of_alternating_action_of_residual_seed (h := h) hG hu hYseed hbound hL
          (Or.inl rfl) ha).elim
    | seven σ _ ha =>
        exact (s.false_of_alternating_action_of_residual_seed (h := h) hG hu hYseed hbound hL
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

/-- The original extraspecial marking excludes ordinary status on this
same selected component using only its own residual's two local controls. -/
theorem PreExclusionSource.extraspecial_not_ordinary_of_marked_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized 3)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hYseed : (pResidual 2 d.MZ).map d.MZ.subtype ≤
      centralizer (centralInvolutions T : Set G))
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  intro hL
  have h20 := s.ordinary20_of_marked_residual_seed (h := h)
    hG hempty hM hJ hu hYseed hbound hL
  exact s.no_extraspecial_ordinary_postRankOne hG h hex c hZ hL
    (h20.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL (Or.inl rfl))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
