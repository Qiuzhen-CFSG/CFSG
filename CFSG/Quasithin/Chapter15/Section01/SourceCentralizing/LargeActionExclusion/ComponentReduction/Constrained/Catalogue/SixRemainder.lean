module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SmallRemainder
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeBlock

/-!
# The remaining six-point constrained row

The whole binary-three block, its two literal parabolics and both source
centralizer clauses discharge the L₃ branch of the reduced FF catalogue.
Only the six-point central quotient remains. Its original C.2.7 input,
MS pair and compatible quotient marking are retained, including the
possible cubic cover. No A₆ reconstruction or exceptional-row exclusion
is assumed. Both original source primes use the same reduction.

Source: Aschbacher--Smith 15.1.20(2) and15.1.22, printed pp.1094--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Every reduced constrained FF row is assembled except the ordinary or
cubic A₆ row, which retains its genuine input and literal marking. -/
theorem PreExclusionSource.constrained_catalogue_or_six_ms
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedAlternatives ∨
      (Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
        SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
        ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃* alternatingGroup (Fin 6),
          ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
            ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
              e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k))) := by
  rcases s.constrained_catalogue_or_small_ms (h := h)
    hG hempty hM hJ hu hne hmany hfull hres hf with ha | ⟨hi,hm,hsmall⟩
  · exact Or.inl ha
  · rcases hsmall with ⟨e,_,_⟩ | hsix
    · obtain ⟨_,_,_,_,_,_,ha⟩ := s.constrained_binaryThree (h := h)
        hG hempty hM hJ hu hfull hf e
      exact Or.inl ha
    · exact Or.inr ⟨hi,hm,hsix⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- Original-marker assembly through the L₃ row, with the full six-point
MS remainder and earlier residual premise still explicit. -/
theorem PreparedChosenModule.source_preExclusion_constrained_catalogue_or_six_ms
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.ConstrainedAlternatives ∨
          (Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
            SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
            ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃* alternatingGroup (Fin 6),
              ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
                ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
                  e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf => s.constrained_catalogue_or_six_ms (h := h)
    hG hempty hM hJ hu hne hmany hfull hres hf⟩

end CFSG.Quasithin.Chapter15.Section01
