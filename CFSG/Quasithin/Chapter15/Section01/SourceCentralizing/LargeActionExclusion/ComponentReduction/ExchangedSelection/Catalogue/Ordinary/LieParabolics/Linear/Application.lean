module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.GraphFive
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics

/-!
# The ordinary binary-linear row under the original placement theorem

For an inner S-action the two endpoint minimal parabolics form the actual
source family, and the independent source placement theorem puts each in
M ∩ L or M_L. Their generating identity and the literal cubic residual
calculation complete row (7). For an outer S-action the direct flag-reversal
argument already proves that same row. Both source primes and the original
marking are retained throughout.

The sole independent input here is precisely 15.1.22(*), owned and finally
discharged by qt-e-15122-pre-exclusion-catalogue in Catalogue/ParabolicPlacement.
No model, local callback, or inner-action hypothesis is left in the row.
Degree five now uses the complete source family for either action type.
The degree-four outer source-family construction, Ru and the exhaustive
assembly remain with qt-e-15122-ordinary-pre-exclusion.

Source: Aschbacher--Smith 15.1.22(7), printed pp.1099--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The full ordinary binary-linear source row, conditional only on the
independently owned original source-parabolic placement. -/
theorem PreExclusionSource.ordinary22_of_binaryLinear
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) :
    d.Ordinary22Alternatives := by
  have apply_geometry (geo : d.OrdinaryLinearParabolicGeometry e) : d.Ordinary22Alternatives := by
    obtain ⟨_,hML,_,hC,_⟩ :=
      s.binaryLinear_parabolic_refinement (h := h) hp hG hM hJ hu hL hn e
    exact s.linear_of_parabolic_geometry (h := h) hG hM.1.2 hu hL hn e hML hC hplacement geo
  rcases hn with rfl | rfl
  · by_cases hi : d.S ≤ d.L ⊔ centralizer (d.L : Set G)
    · obtain ⟨geo⟩ := s.binaryLinear_inner_parabolic_geometry (h := h) hG hM hu hL (.inl rfl) e hi
      exact apply_geometry geo
    · exact s.ordinary22_binaryLinear_of_outer (h := h) hp hG hM hJ hu hL (.inl rfl) e hi
  · obtain ⟨geo⟩ := s.binaryLinear_five_parabolic_geometry (h := h) hG hM hu hL e
    exact apply_geometry geo

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the complete linear row at the original source marker, retaining
all markings and the independent source-placement premise. -/
theorem PreparedChosenModule.source_preExclusion_ordinary22_binaryLinear
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
        (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) →
        ∀ (n : ℕ), (n = 4 ∨ n = 5) →
          (d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) → d.Ordinary22Alternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hplacement n hn e =>
    s.ordinary22_of_binaryLinear (h := h) hp hG hM hJ hu hL hn e hplacement⟩

end CFSG.Quasithin.Chapter15.Section01
