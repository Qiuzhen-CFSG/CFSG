module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Suzuki.Borel
public import Theory.SpecificGroups.Suzuki.ComponentThompson
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# The ordinary simple Suzuki exclusion

The source centralizer G₁ has odd prime ranks at most two. Thus the
ordinary component has at most two conjugates. The concrete Suzuki Sylow
center and elementary replacement give Borel normalization of J(S), even
if S exchanges components. The original Thompson control, two-perfectness
and centralizer comparison then give the source contradiction.

This proves the simple Suzuki part of 15.1.21, with no assumed Thompson
normalization, exchanged-source witness or cubic selection. Nonsimple
central covers remain separate. Source: Aschbacher--Smith 15.1.21(i),
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

/-- Every ordinary selected component has at most two S-conjugates. -/
theorem PreExclusionSource.ordinary_normalizer_relIndex_le_two
    (_s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    (normalizer (d.L : Set G)).relIndex d.S ≤ 2 := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hi : (normalizer (d.L.subgroupOf d.G1 : Set d.G1)).index ≤ 2 := by
    have ho : (d.L.subgroupOf d.G1).Normal ∨
        (normalizer (d.L.subgroupOf d.G1 : Set d.G1)).index = 2 :=
      hL.normal_or_index_two_of_odd_rank_le_two hsq.stronglyQuasithin
    rcases ho with hn | hn
    · rw [normalizer_eq_top_iff.mpr hn,index_top]
      decide
    · exact hn.le
  have hr : (normalizer (d.L.subgroupOf d.G1 : Set d.G1)).relIndex (d.S.subgroupOf d.G1) ≤
      (normalizer (d.L.subgroupOf d.G1 : Set d.G1)).index := by
    simpa only [relIndex_top_right] using
      (relIndex_le_of_le_right (show d.S.subgroupOf d.G1 ≤ ⊤ from le_top) index_ne_zero_of_finite
        (H := normalizer (d.L.subgroupOf d.G1 : Set d.G1)))
  have hn : (normalizer (d.L : Set G)).subgroupOf d.G1 =
      normalizer (d.L.subgroupOf d.G1 : Set d.G1) :=
    subgroupOf_normalizer_eq (show d.L ≤ d.G1 from d.L_component.1)
  have hh := hr.trans hi
  rw [← hn,relIndex_subgroupOf (show d.S ≤ d.G1 from d.S_le_G1)] at hh
  exact hh

/-- Exclusion of the simple Suzuki model from the literal rank-one row. -/
theorem PreExclusionSource.false_of_suzuki_simple
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) {m : ℕ} (hm : 0 < m)
    (e : d.L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hB : d.ML = d.ordinaryBorel) : False := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup d.L := e.isSimpleGroup
  have hz : center d.L = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative d.L (center_eq_top_iff.mp hh))
  have hcore : pCore 2 d.L = ⊥ := (s.ordinary hL).center_eq.symm.trans hz
  let eq := ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).trans e
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  have hj := BenderSuzuki.MatrixGroups.suzuki_component_borel_normalizes_thompson
    d.G1 d.L d.S d.L_component.1 d.S_le_G1 hL (T.isPGroup'.to_le d.S_le_T)
    (s.ordinary_normalizer_relIndex_le_two (h := h) hG hL) P (hP ▸ d.SL_le_S) hm e
  change (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype ≤ _ at hj
  rw [hP'] at hj
  exact s.no_thompson_borel (h := h) hG hM hJ
    (s.suzuki_borel_twoPerfect (h := h) hL hm eq) (hB ▸ d.ML_le_MZ) hj
    (s.suzuki_borel_centralizers (h := h) hL hm eq)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
