module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Geometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.ModelControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement

/-!
# Conditional assembly of the ordinary Lie parabolic rows

For a rank-two model, (*) places the escaping partner in M. Its maximality
and M ∩ L < L identify that partner with M ∩ L. For a binary linear model,
(*) places every member of the generating family in one of the two local
intersections, so those intersections generate L. The same family argument
makes the literal O^{3′}(M ∩ L) escape M_L in both cases. The proved intrinsic
model control then gives the exact centralizer equality and omega-center order.

The model-specific parabolic constructions remain explicit geometric
obligations; this module does not assert that they have been constructed.
Only (*) remains as the independent placement producer's input. The source
rows are individual hypotheses, with no exhaustive catalogue assumed.
Source: Aschbacher--Smith, 15.1.22(4),(7), printed pp.1099--1100.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

omit [Finite G] in
private theorem eq_of_coatom_subgroupOf {L P Q : Subgroup G}
    (hP : P ≤ L) (hQ : Q < L) (hmax : IsCoatom (P.subgroupOf L)) (hPQ : P ≤ Q) :
    Q = P := by
  have hn : Q.subgroupOf L ≠ ⊤ := by
    intro he
    exact (not_le_of_gt hQ) (subgroupOf_eq_top.mp he)
  have he := (hmax.le_iff_eq hn).mp (comap_mono hPQ)
  have hm := congrArg (Subgroup.map L.subtype) he
  simpa only [map_subgroupOf_eq_of_le hQ.le, map_subgroupOf_eq_of_le hP] using hm

/-- Placement of the actual partner and its maximality identify M ∩ L and prove ordinary row (4). -/
theorem PreExclusionSource.binaryRankTwo_of_parabolic_geometry
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L)
    (hmarked : d.ML = d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G))
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML)
    (geo : d.OrdinaryRankTwoParabolicGeometry) : d.Ordinary22Alternatives := by
  have hloc := s.local_intersections (h := h) hG hu hTM
  have hPM : geo.other ≤ M ⊓ d.L :=
    (hplacement geo.other geo.other_source).resolve_right geo.other_escape
  have he : M ⊓ d.L = geo.other :=
    eq_of_coatom_subgroupOf geo.other_source.le_component hloc.2.2.2.2.1
      geo.other_maximal hPM
  have hout : ¬ sSup ({geo.other} : Set (Subgroup G)) ≤ d.ML := by
    simpa only [csSup_singleton] using geo.other_escape
  have hR := (s.parabolic_family_residual_escape (h := h) hG hu hTM hplacement
    {geo.other} (by intro P hP; rcases hP with rfl; exact geo.other_source) hout).2
  have hcontrol := s.binaryRankTwo_model_control (h := h) hTM hu hL hm
  apply Ordinary22Alternatives.binaryRankTwo hm hmarked geo.marked_parabolic
    (he.symm ▸ geo.other_parabolic) geo.marked_maximal (he.symm ▸ geo.other_maximal)
  · intro heq
    exact geo.other_escape (heq.symm ▸ hPM)
  · exact hcontrol.2 hR

/-- Placement of the actual generating family proves generation, residual escape and ordinary row (7). -/
theorem PreExclusionSource.linear_of_parabolic_geometry
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hmarked : d.OrdinaryLinearParabolic e d.ML)
    (hcentral : d.L ⊓ centralizer ((center d.SL).map d.SL.subtype : Set G) ≤ d.ML)
    (hplacement : ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML)
    (geo : d.OrdinaryLinearParabolicGeometry e) : d.Ordinary22Alternatives := by
  have hloc := s.local_intersections (h := h) hG hu hTM
  have hout : ¬ sSup geo.family ≤ d.ML := by
    intro hh
    have hle : d.L ≤ d.ML := geo.generated ▸ sup_le le_rfl hh
    exact (not_le_of_gt hloc.2.2.1) hle
  have hR := (s.parabolic_family_residual_escape (h := h) hG hu hTM hplacement
    geo.family geo.members hout).2
  have hgen : d.ML ⊔ (M ⊓ d.L) = d.L := by
    apply le_antisymm (sup_le inf_le_right inf_le_right)
    apply le_trans geo.generated.ge
    apply sup_le le_sup_left
    apply sSup_le
    intro P hP
    rcases hplacement P (geo.members hP) with hPM | hPL
    · exact hPM.trans le_sup_right
    · exact hPL.trans le_sup_left
  exact Ordinary22Alternatives.linear n hn e hmarked
    (geo.flag_overgroups _ hloc.2.2.2.1 hloc.2.2.2.2.1) hcentral hgen
    ((s.linear_model_control (h := h) hTM hu hL hn e).2 hR)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
