module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticLinear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial

/-!
# Applying all seven rows before exchanged selection

The original prime-five actor excludes the ordinary rows, and its faithful
sixteen-element moving image excludes the constrained rows. Apply the
assembled source catalogue to that same component. This application still
requires the actual prime-five source and faithful image: it does not
construct the missing prime-five marker from an arbitrary large action.

For the extraspecial action, use the already constructed original marker
and its same-component exclusions. The full source catalogue now supplies
the missing exhaustive disjunction; no cubic-lift movement assumption or
later exchanged source enters the argument.

Both applications retain the whole-core A₆ reconstruction and original
15.1.14 residual. Final discharge and large-action selection remain with
qt-e-1515-exchanged-component-selection and qt-e-1515-large-component-reduction.
Source: Aschbacher--Smith 15.1.22--24, printed pp.1098--1101.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Discharge both catalogue branches of the published prime-five exclusion
on the original component and its actual faithful moving image. -/
theorem PreExclusionSource.not_quintic_of_image_sixteen
    (s : d.PreExclusionSource h.normalized 5)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
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
    {B : Subgroup G} (hBV : B ≤ V) (hBL : B ≤ normalizer (d.L : Set G))
    (hcard : Nat.card (internalActionImage B d.L hBL) = 16) : False := by
  rcases s.source22 (h := h) (Or.inr rfl) ha
      hG hempty hM hJ hu hne hmany hfull hres with ⟨_,hc⟩ | ⟨hL,ho⟩
  · exact s.not_constrained_of_prime_five_image_sixteen (h := h)
      hG hM hJ hfull hu hBV hBL hcard hc.toAlternatives
  · exact s.not_ordinary22_of_prime_five (h := h) hG hM hJ hu hL ho

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal extraspecial source action is impossible once the independent
whole-core reconstruction and earlier residual inputs are supplied. All row
exclusions apply to the component selected by that action's original marker. -/
theorem PreparedChosenModule.source_not_extraspecial_of_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ¬ SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) := by
  let := h.elementary
  intro hex
  obtain ⟨c,m,d,_,_,_,_,_,_,_,_,_,_,s,ho,hc⟩ :=
    h.source_extraspecial_catalogue_obstruction
      hG T hempty hM hmany hJ hu hne hfull hex hres
  rcases s.source22 (h := h) (Or.inl rfl) ha
      hG hempty hM hJ hu hne hmany hfull hres with ⟨_,hr⟩ | ⟨hL,_⟩
  · exact hc hr.toAlternatives
  · exact ho hL

end CFSG.Quasithin.Chapter15.Section01
