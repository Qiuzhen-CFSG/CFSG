module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceLargeChosenCatalogueSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixRemainder
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Exhaustion.Source
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# Exhaustiveness of the actual selected-component catalogue

The full proper local catalogue leaves only the six-point central quotient.
Its centerless case has the proved natural whole core. In its cubic case,
the original central seed forces whole-core exhaustion, and the original
exceptional-block exclusion applies. Thus the literal pre-exclusion source
has the constrained alternatives whenever its generalized Fitting subgroup
is its two-core. The C-component dichotomy then gives the requested
ordinary-or-constrained alternative on that same selected component.

Only the permitted earlier residual statement is retained. No universal
MS classification or whole-core reconstruction is assumed.
Source: Aschbacher--Smith 15.1.20--22, printed pp.1094--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Exceptional
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The genuine original pre-exclusion source supplies the complete
constrained alternatives without an external reconstruction premise. -/
theorem PreExclusionSource.original_constrained_catalogue
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ConstrainedAlternatives := by
  rcases s.constrained_catalogue_or_six_ms (h := h)
    hG hempty hM hJ hu hne hmany hfull hres hf with hc | ⟨hi,hms,_,t,_⟩
  · exact hc
  let e := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  rcases hms.alternating_center_cases e with hz | hz
  · obtain ⟨he,hc,hm⟩ := naturalCore_of_distanceFour_knownSimple
      SixteenClosure.distanceFourInput_knownSimple G d.L d.Q1 hms e hz
    have hs := hms.short_of_core he hc s.quasisimple hm.alternating_six_irreducible
    have hb : IsAlternatingBlock d.L 6 := ⟨by decide,hs,hm⟩
    obtain ⟨_,_,_,_,_,_,_,_,_,_,ha⟩ :=
      s.constrained_six_of_block (h := h) hG hempty hM hJ hu hfull hb
    exact ha
  · have hx := s.original_cubic_coreExhaustion (h := h) hG hM.1.2 hu hi hms t hz
    obtain ⟨he,hc,hirr,h64,hfaith⟩ := core_facts_of_exhaustion hms e hz hx
    have hs := hms.short_of_core he hc s.quasisimple hirr
    have hb : IsExceptionalAhat6Block d.L :=
      ⟨hs,s.quasisimple,hz,
        ⟨(centralPreimageQuotientEquiv (pCore 2 d.L)).symm.trans t⟩,h64,hfaith⟩
    exact (s.not_constrained_exceptionalSix (h := h) hG hM hu hb).elim

/-- Ordinary component status or the genuine constrained catalogue holds
for the same original selected component. -/
theorem PreExclusionSource.original_component_or_constrained_catalogue
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    IsComponent d.G1 (d.L.subgroupOf d.G1) ∨ d.ConstrainedAlternatives := by
  rcases d.L_component.2.component_or_generalizedFitting_eq_pCore s.odd_core with hc | hf
  · exact Or.inl hc
  · have hfL : generalizedFitting d.L = pCore 2 d.L := by
      let e : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
      exact (map_generalizedFitting_equiv e).symm.trans
        ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e))
    exact Or.inr (s.original_constrained_catalogue (h := h)
      hG hempty hM hJ hu hne hmany hfull hres hfL)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
