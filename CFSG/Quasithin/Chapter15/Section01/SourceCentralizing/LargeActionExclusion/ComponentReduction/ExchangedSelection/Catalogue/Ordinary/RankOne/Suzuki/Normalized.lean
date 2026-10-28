module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Suzuki.Borel
public import Theory.GroupAction.InnerSylowNormalizer
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Exclusion of the component-normalizing Suzuki branch

Odd outer order makes the original S-action inner on the Suzuki quotient.
Perfectness lifts innerness across the central two-core. The lifted Borel
therefore normalizes S itself, and hence J(S). This discharges the model
Thompson premise in the ordinary source contradiction whenever S normalizes
the selected component; in particular it excludes components normal in G₁.

All Sylow subgroups and Borels are the literal source subgroups. Central
two-covers, including those of Sz(8), are retained. The nontrivial S-orbit
case is not asserted here. Source: Aschbacher--Smith 15.1.21(i),
printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Model normalization of the actual Sylow subgroup, with the original cover. -/
theorem PreExclusionSource.suzuki_borel_normalizes_sylow
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hSL : d.S ≤ normalizer (d.L : Set G)) {m : ℕ} (hm : 0 < m)
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    d.ordinaryBorel ≤ normalizer (d.S : Set G) := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  have hn := sylowNormalizer_le_normalizer_of_odd_outer d.L d.S
    (T.isPGroup'.to_le d.S_le_T) hSL P (hP ▸ d.SL_le_S) ec
    (BenderSuzuki.MatrixGroups.suzuki_odd_outer_index m (by omega))
  change (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype ≤ _ at hn
  rw [hP'] at hn
  exact hn

/-- Original Thompson control excludes every Suzuki row normalized by S.
The model's Thompson-normalization premise is proved here. -/
theorem PreExclusionSource.false_of_suzuki_normalized
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hSL : d.S ≤ normalizer (d.L : Set G)) {m : ℕ} (hm : 0 < m)
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hB : d.ML = d.ordinaryBorel) : False :=
  s.no_thompson_borel (h := h) hG hM hJ
    (s.suzuki_borel_twoPerfect (h := h) hL hm e) (hB ▸ d.ML_le_MZ)
    ((s.suzuki_borel_normalizes_sylow (h := h) hL hSL hm e).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ d.S))
    (s.suzuki_borel_centralizers (h := h) hL hm e)

/-- Normality is relative to G₁, never to the ambient simple group. -/
theorem PreExclusionSource.false_of_suzuki_relative_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hn : (d.L.subgroupOf d.G1).Normal) {m : ℕ} (hm : 0 < m)
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hB : d.ML = d.ordinaryBorel) : False :=
  s.false_of_suzuki_normalized (h := h) hG hM hJ hL
    (d.S_le_G1.trans ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp hn)) hm e hB

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
