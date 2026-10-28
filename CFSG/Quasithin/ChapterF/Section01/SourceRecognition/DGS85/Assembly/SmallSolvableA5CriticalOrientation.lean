module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.A5BetaSmallAlphaExclusion

/-!
# The directed critical orientation of the small-solvable / A₅ pair

Every critical edge at distance one starts at the A₅ type. The other
orientation contradicts the short-path alpha selection. Translating an
existing directed critical edge therefore makes the literal base edge
from type true to type false critical. No reversal of criticality is used.
Source: DGS, *Groups and Graphs* (1985), (11.4)--(11.5), pp.171--172;
Aschbacher--Smith 15.2.4--8, printed pp.1106--1110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

/-- Every directed critical pair has A₅ at alpha and a small-solvable
quotient at beta. This follows from alpha selection, not pair reversal. -/
theorem small_solvable_a5_critical_orientation (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (ha : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)))
    {a beta : Vertex F} (hc : IsCriticalPair F a beta)
    (hb : DGS85.b F = 1) : a.type = true ∧ beta.type = false := by
  have hadj := SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
  have hat : a.type = true := by
    by_contra hnot
    have hat : a.type = false := Bool.eq_false_iff.mpr hnot
    have hbt : beta.type = true := by
      have hne := hadj.1
      cases hbt : beta.type <;> simp_all
    exact CommutingOneProfile.source_small_solvable_alpha_a5_beta_exclusion
      (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) (Reduction.reducedFullEarlierLocalTheorems h)
      hc hb (Reduction.reduced_critical_commuting_of_small_solvable h false hm hc)
      (small_solvable_graph_quotients h false hm a hat)
      (a5_graph_quotient h true ha.some beta hbt).some
  refine ⟨hat,?_⟩
  have hne := hadj.1
  cases hbt : beta.type <;> simp_all

/-- The literal A₅-to-small base edge is critical, with commuting centers.
Criticality is transported by a group element and is never reversed. -/
theorem small_solvable_a5_base_critical (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (ha : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5)))
    (hb : DGS85.b F = 1) :
    IsCriticalPair F (base F true) (base F false) ∧
      ⁅Z F (base F true),Z F (base F false)⁆ = ⊥ := by
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
  obtain ⟨a,beta,hc⟩ := source_exists_criticalPair (Reduction.reduced_triple h)
  obtain ⟨hat,hbt⟩ := small_solvable_a5_critical_orientation h hm ha hc hb
  have hadj := SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
  obtain ⟨g,hga,hgb⟩ := incident_common_translate F hadj.2
  rw [hat] at hga
  rw [hbt] at hgb
  have hc' := CommutingNontrivial.criticalPair_translate F hc g⁻¹
  rw [←hga,←hgb,inv_smul_smul,inv_smul_smul] at hc'
  exact ⟨hc',Reduction.reduced_critical_commuting_of_small_solvable h false hm hc'⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
