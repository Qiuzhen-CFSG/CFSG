module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts

/-!
# Centers at all neighbors of the terminal vertex are central

In a noncommuting local Section Eight context, centrality of the first
neighbor center implies centrality at every neighbor of the terminal vertex.
Only the initial centrality and adjacency are assumed; no fixed-closure
witness, branch, or critical-length premise is needed. The canonical public
interface is retained as a wrapper using its actual local graph; the same
local theorem is available for the generated-group proof of (8.4).

Edge transitivity sends the initial edge to the chosen terminal edge. The
orientation that would send its central endpoint to the terminal vertex is
impossible: the initial center lies in the terminal stabilizer and does not
commute with the terminal center. In the remaining orientation, center and
stabilizer covariance transport both containment and commutation, giving the
actual ambient center inclusion at the chosen neighbor.

This is the terminal-neighbor centrality used in Stellmacher (8.4)(9),
Journal of Algebra 190 (1997), pp.39–40, refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- Every terminal neighbor has its vertex center in its stabilizer center. -/
public theorem eight_four_terminal_neighbor_central_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent ctx.criticalPath.a' neighbor) :
    ZAt ctx.Γ neighbor ≤ CenterAmbient (GAt ctx.Γ neighbor) := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hend : ⁅z Γ cp.a', stabilizer Γ cp.a'⁆ ≠ ⊥ := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact bot_unique ((Subgroup.commutator_mono le_rfl
      ((lemma_seven_four h Γ cp).first_containment.1.trans
        (lemma_seven_four h Γ cp).first_containment.2)).trans_eq hc)
  have hc : ⁅z Γ cp.firstStep, stabilizer Γ cp.firstStep⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
  obtain ⟨g, hedge | hedge⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · have hact : ⁅z Γ neighbor, stabilizer Γ neighbor⁆ = ⊥ := by
      rw [← hedge.2,z_act,stabilizer_act,conjugateBy,← Subgroup.map_commutator,
        hc,Subgroup.map_bot]
    have hZP : z Γ neighbor ≤ stabilizer Γ neighbor := by
      rw [← hedge.2,z_act,stabilizer_act,conjugateBy]
      exact Subgroup.map_mono (hcenter.trans (Subgroup.map_subtype_le _))
    intro z hz
    refine ⟨⟨z,hZP hz⟩,?_,rfl⟩
    change (⟨z,hZP hz⟩ : stabilizer Γ neighbor) ∈ Subgroup.center (stabilizer Γ neighbor)
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hact hz) x x.property
  · have hact : ⁅z Γ (Γ.act g cp.firstStep), stabilizer Γ (Γ.act g cp.firstStep)⁆ = ⊥ := by
      rw [z_act,stabilizer_act,conjugateBy,← Subgroup.map_commutator,hc,Subgroup.map_bot]
    rw [hedge.2] at hact
    exact False.elim (hend hact)

/-- Canonical interface, retaining the original graph and all hypotheses. -/
public theorem eight_four_terminal_neighbor_central
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (neighbor : ctx.Γ.Vertex)
    (hadj : ctx.Γ.adjacent ctx.criticalPath.a' neighbor) :
    ZAt ctx.Γ neighbor ≤ CenterAmbient (GAt ctx.Γ neighbor) :=
  eight_four_terminal_neighbor_central_local ctx.toLocalContext hcenter neighbor hadj

end Stellmacher.SectionEight
