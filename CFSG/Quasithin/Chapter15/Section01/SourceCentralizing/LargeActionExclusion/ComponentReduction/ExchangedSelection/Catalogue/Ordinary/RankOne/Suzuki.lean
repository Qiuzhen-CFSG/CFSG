module
public import Theory.SpecificGroups.Suzuki.BorelResidualCentralizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary

/-!
# The Suzuki Borel residual on the selected ordinary component

Transport the model comparison to the literal S_L and Borel of the component
selected before exclusions. Its two-residual is two-perfect and lies in M_Z
when the rank-one row identifies M_L with that Borel. Original Thompson
control then gives the source contradiction once the model proves that the
Borel normalizes J(S). That last model premise is still explicit here and
remains with the ordinary rank-one exclusion owner.

The quotient is always L/O₂(L), so in particular the exceptional central
two-covers of Sz(8) are retained. Source: Aschbacher--Smith 15.1.21(i),
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

/-- The Sylow centralizer comparison for the actual ordinary Suzuki component. -/
theorem PreExclusionSource.suzuki_borelResidual_centralizers
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) {m : ℕ} (hm : 0 < m)
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    d.S ⊓ centralizer ((pResidual 2 d.ordinaryBorel).map d.ordinaryBorel.subtype : Set G) ≤
      d.S ⊓ centralizer (d.L : Set G) := by
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le d.SL_le_L]
  have hB : (normalizer (P : Set d.L)).map d.L.subtype = d.ordinaryBorel := by
    change (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype = _
    rw [hP']
    rfl
  have hR : ((pResidual 2 (normalizer (P : Set d.L))).map
      (normalizer (P : Set d.L)).subtype).map d.L.subtype =
      (pResidual 2 d.ordinaryBorel).map d.ordinaryBorel.subtype := by
    rw [map_embedded_pResidual, hB]
  have hc := BenderSuzuki.MatrixGroups.suzuki_borelResidual_relative_centralizer
    d.G1 d.L d.L_component.1 hL (s.ordinary hL).center_eq hm e P
  rw [hR] at hc
  exact le_inf inf_le_left
    ((le_inf (inf_le_left.trans d.S_le_G1) inf_le_right).trans hc)

/-- Use the Suzuki geometry in the actual source contradiction. The remaining
model obligation is the Borel's Thompson normalization; original ambient
Thompson control supplies every other normalizer premise. -/
theorem PreExclusionSource.false_of_suzuki_borel_thompson
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) {m : ℕ} (hm : 0 < m)
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hB : d.ML = d.ordinaryBorel)
    (hBJ : d.ordinaryBorel ≤ normalizer (elementaryAbelianMaxJ d.S : Set G)) : False := by
  have hJS := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  have hNJ := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  exact s.false_of_thompson_borel (h := h) hM.1.2 hJS hNJ
    (isPPerfect_embedded_pResidual 2 d.ordinaryBorel)
    ((map_subtype_le _).trans (hB ▸ d.ML_le_MZ))
    ((map_subtype_le _).trans hBJ)
    (s.suzuki_borelResidual_centralizers (h := h) hL hm e)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
