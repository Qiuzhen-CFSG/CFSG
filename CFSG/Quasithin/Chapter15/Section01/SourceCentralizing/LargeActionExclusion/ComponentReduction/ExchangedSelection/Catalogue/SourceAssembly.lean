module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.OrdinaryComplete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SourceAssembly

/-!
# The seven source rows on the original pre-exclusion component

Split the actual C-component into its ordinary and constrained branches.
The ordinary refinement supplies rows (4)--(7); the constrained refinement
supplies rows (1)--(3), with the rank-two row split by its three models.
Use the existing full conclusions directly: the A₇ weight-two action,
the opposite A₆/G₂ markings, both binary flags, covering kernels and
embedded prime-to-three residuals are retained.

The original marker is selected once, so the catalogue, shared placement
and escaping-family centralizer theorem concern the same component and
prime. The conversion to the older constrained exclusion interface is
used by the actual row-exclusion consumers in `Applications`.

The whole-core A₆ reconstruction and original 15.1.14 residual remain
explicit independent inputs. Their producers are qt-e-ms-small-a6-reconstruction
and qt-e-1514-global-thompson-residual, retained by the constrained-catalogue
and large-action assembly owners. This is conditional source assembly,
not an unconditional proof of 15.1.22 or Theorem E.

Source: Aschbacher--Smith 15.1.20--22, printed pp.1094--1100.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Feed the full source refinement to the existing exclusion consumers.
The source conclusion itself continues to retain its additional geometry. -/
theorem ConstrainedSource22Alternatives.toAlternatives
    (a : d.ConstrainedSource22Alternatives) : d.ConstrainedAlternatives := by
  cases a with
  | seven base => exact .alternatingSeven base
  | linearThree base => exact .linearThree base
  | six block geometry => exact .alternatingSix block geometry.centralizers
  | g2 block geometry => exact .g2 block geometry.centralizers
  | linear n hn _ t hm hs hg => exact .linear n hn t hm hs hg

/-- All seven original source rows at either prime, with actual component
status retained for the downstream row exclusions. No model, placement,
normalization or centralizer premise is added. -/
theorem PreExclusionSource.source22
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
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
        centralizer (thompsonFixed T V : Set G)) :
    (generalizedFitting d.L = pCore 2 d.L ∧ d.ConstrainedSource22Alternatives) ∨
      (IsComponent d.G1 (d.L.subgroupOf d.G1) ∧ d.Ordinary22Alternatives) := by
  rcases d.L_component.2.component_or_generalizedFitting_eq_pCore s.odd_core with hc | hf
  · exact Or.inr ⟨hc, s.source_ordinary22 (h := h)
      hG hempty hM hJ hu hne hmany hres hc hp⟩
  · have hfL : generalizedFitting d.L = pCore 2 d.L := by
      let e : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
      exact (map_generalizedFitting_equiv e).symm.trans
        ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e))
    exact Or.inl ⟨hfL, s.constrained_source22 (h := h) hp ha
      hG hempty hM hJ hu hne hmany hfull hres hfL⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original marker supplies every source row, (*) and (!) on one
component, before excluding prime five or the extraspecial row. -/
theorem PreparedChosenModule.source_preExclusion_catalogue
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
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
      ((generalizedFitting d.L = pCore 2 d.L ∧ d.ConstrainedSource22Alternatives) ∨
        (IsComponent d.G1 (d.L.subgroupOf d.G1) ∧ d.Ordinary22Alternatives)) ∧
      (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧
      ∀ (F : Set (Subgroup G)), F ⊆ d.sourceParabolics → ¬ sSup F ≤ d.ML →
        Nat.card d.plusOmega = 2 →
        (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
          (¬ d.localThreeResidual ≤ d.ML) ∧
          d.S ⊓ centralizer (d.localThreeResidual : Set G) =
            d.S ⊓ centralizer (d.L : Set G) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,
    s.source22 (h := h) hp ha hG hempty hM hJ hu hne hmany hfull hres,
    s.source_parabolic_placement (h := h) hG hempty hM hJ hu hne hmany hres hp,?_⟩
  intro F hF hout hcard
  exact s.source_parabolic_family_centralizer (h := h)
    hG hempty hM hJ hfull hu hne hmany hres hp hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01
