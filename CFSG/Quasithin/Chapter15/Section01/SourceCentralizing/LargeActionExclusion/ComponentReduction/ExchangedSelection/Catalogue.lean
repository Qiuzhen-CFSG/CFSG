module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Preparation
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.SourceGeometry.Source
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Source
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.RankSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.OrdinarySource

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.SourceRows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.OrdinaryComplete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Applications

/-!
# Source preparation for the pre-exclusion catalogue

Apply the relative C.2.7 preparation and the common local-intersection
geometry to the component actually constructed from the original marker.
All subgroup inclusions, normalizers and star maps use that same component.
The prime is unrestricted, so in particular the application is available
for both three and five before the unwanted-row contradictions.
The fixed-pair extensions now prove (*) for both ordinary and constrained
components, even when S moves L. The constrained argument uses the literal
P N_S(L), its actual two-residual, and Baumann normalization obtained by
odd-orbit averaging of the original central seed. The independently proved
full-local-family nonblock theorem also discharges the earlier ordinary
catalogue premise. Together with the source plus geometry, this proves (!)
under its stated order-two and escaping-family hypotheses.
The actual ordinary row consumer now supplies all four ordinary alternatives
at both source primes, with cubic Rudvalis and the full-family nonblock
premise discharged. The same-marker consumer retains shared placement.
The full constrained refinement and all four ordinary rows are now assembled
on one original marker, retaining the extra A₇/A₆/G₂ clauses and shared
placement. The actual prime-five faithful-image and extraspecial consumers
use this exhaustive disjunction. Whole-core A₆ reconstruction and the genuine
earlier 15.1.14 residual remain explicit independent inputs; their final
discharge, the prime-five marker and full large-action selection remain open.
Source: Aschbacher--Smith 15.1.18--22, printed pp.1093--1100.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]

/-- The general marker constructs both proper source intersections and,
conditionally on the actual constrained branch and Q₁-normalization, the
genuine C.2.7 input and its radical omega-center geometry. -/
theorem PreparedChosenModule.source_preExclusion_catalogue_preparation
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
      (HasCharacteristicTwo d.ML ∧ d.SL ≤ d.ML ∧ d.ML < d.L ∧
        d.SL ≤ M ⊓ d.L ∧ M ⊓ d.L < d.L ∧
        d.L ⊓ centralizer (centralInvolutions T : Set G) ≤ d.ML) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.Q1 ≤ normalizer (d.L : Set G) →
        Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
        (d.L ⊔ d.Q1).pCoreIn 2 ≤ d.Q1 ∧
        omegaOneCenterAmbient d.Q1 ≤
          (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype) := by
  obtain ⟨d, hZ, hr, s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d, hZ, hr, s, s.local_intersections (h := h) hG hu hM.1.2, ?_⟩
  intro hfit hnL
  have hi := s.constrained_input_of_normalizes (h := h) hG hfit hnL
  exact ⟨hi, d.preExclusion_radical_omega hi⟩

end CFSG.Quasithin.Chapter15.Section01
