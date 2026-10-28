module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Application
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Normalized

/-!
# The ordinary binary-linear source row with placement discharged

The original odd-rank argument makes the binary-linear component normal
in G₁, so S normalizes it. Apply the parent's proved normalizing branch
of 15.1.22(*) to the actual source parabolics, then the constructed linear
geometry gives both proper parabolics, generation and the literal cubic
residual-centralizer identity. The conditional row is preserved unchanged.

The marker application retains the same component, Z₁, row and either
source prime. This uses the published placement result of
qt-e-15122-pre-exclusion-catalogue; it does not assert completion of that
owner's permuted-component branch or of the independent full local-family
nonblock premise. Source: Aschbacher--Smith 15.1.22(7), pp.1099--1100.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The full ordinary binary-linear source row, using the
proved original source-parabolic placement in the normalizing branch. -/
theorem PreExclusionSource.ordinary22_of_binaryLinear_source
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    d.Ordinary22Alternatives := by
  apply s.ordinary22_of_binaryLinear (h := h) hp hG hM hJ hu hL hn e
  exact s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h
    (d.S_le_G1.trans (s.binaryLinear_normal (h := h) hG hL hn e))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the complete linear row at the original source marker, retaining
all markings and discharging source placement by component normality. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_binaryLinear_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ∀ (n : ℕ), (n = 4 ∨ n = 5) →
          (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) → d.Ordinary22Alternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL n hn e =>
    s.ordinary22_of_binaryLinear_source (h := h) hp hG hM hJ hu hL hn e⟩

end CFSG.Quasithin.Chapter15.Section01
