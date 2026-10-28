module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Suzuki
public import Theory.SpecificGroups.Suzuki.BorelCover

/-!
# The full ordinary Suzuki Borel

Perfect central transfer proves that the actual ordinary Borel is
two-perfect, including the Sz(8) central covers. The checked residual
centralizer comparison consequently applies to the full Borel itself.
These are the first and third model premises in the contradiction of
Aschbacher--Smith 15.1.21(i), printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Two-perfectness concerns the whole lifted Borel, not a chosen complement. -/
theorem PreExclusionSource.suzuki_borel_twoPerfect
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) {m : ℕ} (hm : 0 < m)
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    IsPPerfect 2 d.ordinaryBorel := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hb := BenderSuzuki.MatrixGroups.suzuki_coverBorel_isPPerfect
    (s.ordinary hL).center_eq.ge hm e P
  let f := (normalizer (P : Set d.L)).equivMapOfInjective d.L.subtype d.L.subtype_injective
  have hh := hb.of_surjective f.toMonoidHom f.surjective
  change IsPPerfect 2 ((normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype) at hh
  rw [hP'] at hh
  exact hh

/-- The Sylow centralizer comparison for the full lifted source Borel. -/
theorem PreExclusionSource.suzuki_borel_centralizers
    (s : d.PreExclusionSource h.normalized p)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) {m : ℕ} (hm : 0 < m)
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    d.S ⊓ centralizer (d.ordinaryBorel : Set G) ≤ d.S ⊓ centralizer (d.L : Set G) := by
  have hr : (pResidual 2 d.ordinaryBorel).map d.ordinaryBorel.subtype = d.ordinaryBorel := by
    rw [(pResidual_eq_top_iff 2 _).mpr (s.suzuki_borel_twoPerfect (h := h) hL hm e),
      ← MonoidHom.range_eq_map, range_subtype]
  simpa only [hr] using s.suzuki_borelResidual_centralizers (h := h) hL hm e

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
