module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.ResidualRestriction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.SourceGeometry.Source

/-!
# Original marker and escaping-family applications of same-pair placement

In the branch S ≤ N(L), the universal-pair argument discharges placement
for every source parabolic. The literal residual supplement and plus
geometry then give (!) for any escaping family with |Z_L⁺|=2.
The general marker constructs the component, retaining the original
ambient hypotheses and both source primes.

For ordinary components, residual restriction also supplies placement and
(!) from minimality of the literal closures, without assuming S normalizes L.
Minimality, constrained-component restriction and seven-row exhaustion
remain with the catalogue assembly owner qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith, 15.1.22(*), (**), (!), pp.1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The actual family consumer in the normalizing branch, with all
fixed-pair, residual-product and plus-geometry inputs discharged. -/
theorem PreExclusionSource.parabolic_family_centralizer_of_sylow_normalizes
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnL : d.S ≤ normalizer (d.L : Set G)) (hcard : Nat.card d.plusOmega = 2)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) :=
  s.parabolic_family_centralizer_of_placement (h := h) hG hfull hM.1.2 hu
    (s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h hnL) hcard F hF hout

/-- The ordinary escaping-family consumer discharges the fixed-pair and
residual-product inputs, retaining only literal closure minimality. -/
theorem PreExclusionSource.parabolic_family_centralizer_of_ordinary_minimal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hminimal : ∀ P ∈ d.sourceParabolics, ∀ R : Sylow 2 (d.parabolicClosure P),
      (R : Subgroup (d.parabolicClosure P)).map (d.parabolicClosure P).subtype = d.S →
      ChapterB.IsMinimalParabolicOver R ⊤)
    (hcard : Nat.card d.plusOmega = 2)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) :=
  s.parabolic_family_centralizer_of_placement (h := h) hG hfull hM.1.2 hu
    (s.parabolic_placement_of_ordinary_minimal hG hM hJ hu h hcL hminimal) hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies placement and (!) in the normalizing
branch. Normalization is a branch condition, not an assertion about every
source component. The other branch remains with catalogue assembly. -/
theorem PreparedChosenModule.source_preExclusion_normalizing_placement
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
      (d.S ≤ normalizer (d.L : Set G) →
        (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧
        ∀ (F : Set (Subgroup G)), F ⊆ d.sourceParabolics → ¬ sSup F ≤ d.ML →
          Nat.card d.plusOmega = 2 →
          (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
            (¬ d.localThreeResidual ≤ d.ML) ∧
            d.S ⊓ centralizer (d.localThreeResidual : Set G) =
              d.S ⊓ centralizer (d.L : Set G)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hnL => ⟨?_,?_⟩⟩
  · exact s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h hnL
  · intro F hF hout hcard
    exact s.parabolic_family_centralizer_of_sylow_normalizes
      (h := h) hG hM hJ hfull hu hnL hcard F hF hout

/-- Application to the component constructed from the original marker.
The ordinary branch now needs only closure minimality; all local orbit,
fixed-pair and plus-centralizer premises are discharged. Final discharge
of minimality and the other branch remains with the catalogue owner. -/
theorem PreparedChosenModule.source_preExclusion_ordinary_minimal_placement
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        (∀ P ∈ d.sourceParabolics, ∀ R : Sylow 2 (d.parabolicClosure P),
          (R : Subgroup (d.parabolicClosure P)).map (d.parabolicClosure P).subtype = d.S →
          ChapterB.IsMinimalParabolicOver R ⊤) →
        (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧
        ∀ (F : Set (Subgroup G)), F ⊆ d.sourceParabolics → ¬ sSup F ≤ d.ML →
          Nat.card d.plusOmega = 2 →
          (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
            (¬ d.localThreeResidual ≤ d.ML) ∧
            d.S ⊓ centralizer (d.localThreeResidual : Set G) =
              d.S ⊓ centralizer (d.L : Set G)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hcL hmin => ⟨?_,?_⟩⟩
  · exact s.parabolic_placement_of_ordinary_minimal hG hM hJ hu h hcL hmin
  · intro F hF hout hcard
    exact s.parabolic_family_centralizer_of_ordinary_minimal
      (h := h) hG hM hJ hfull hu hcL hmin hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01
