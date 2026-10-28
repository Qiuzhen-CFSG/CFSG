module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionEight.EightThreeCoreBound
public import Stellmacher.SectionEight.EightThreeCoreCollapse
public import Stellmacher.SectionEight.EightThreeActionComparison
public import Stellmacher.SectionFiveToSeven.Result6_1
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSymmetry

/-!
# The residual-core noncontainment in Stellmacher (8.3)

If the next vertex module is central in its stabilizer, the two-core of
the initial residual cannot lie in the next vertex core. This is the
noncontainment used in the central-vertex branch of Section Eight.

Assume containment. The prescribed-module local-family argument bounds
[Qa, Ea] by Za and places Za inside the next core. The center-free core
collapse then gives Qa = Za. Comparing the native quotient actions puts
the Baumann subgroup of the common Sylow in the next core, contrary to
(6.1). A short private helper handles both orientations of the critical
edge; critical noncommutation supplies the hypothesis needed to swap (6.1).

This assembles the proved local bounds and action comparison into the
source statement, keeping the actual critical path and common Sylow.
Source: refs/latex/stellmacher-n-group.tex, (8.3), journal p.38.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem baumann_not_le_next
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) :
    ¬ baumannIn S ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hGa : ⁅stabilizer Γ cp.a, omegaOneCenter S⁆ ≠ ⊥ := by
    intro hc
    have hC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    have hΩP : omegaOneCenter S ≤ stabilizer Γ cp.a :=
      (Subgroup.map_subtype_le _).trans (SevenSix.edge_sylow_data h Γ cp).1.1
    have hn : NormalIn (omegaOneCenter S) (stabilizer Γ cp.a) :=
      ⟨hΩP,(Subgroup.normal_subgroupOf_iff_le_normalizer hΩP).mpr
        (hC.trans (Subgroup.centralizer_le_normalizer _))⟩
    have hZ := z_eq_omega_sylow_of_normal Γ cp.a
      (SevenSix.edge_sylow_data h Γ cp).1 hn
    apply ctx.commutator_ne
    change ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥
    rw [hZ,Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (lemma_seven_four h Γ cp).reverse_containment.1.trans hC
  change ¬ baumannIn S ≤ q Γ cp.firstStep
  rw [q,Γ.twoCoreAt_def]
  change ¬ baumannIn S ≤ twoCoreIn (stabilizer Γ cp.firstStep)
  rcases cp.edge_stabilizers_are_P with he | he
  · rw [he.2]
    exact lemma_six_one S0 S P1 P2 ctx.hypothesisTwo
  · rw [he.1] at hGa
    rw [he.2]
    exact lemma_six_one S0 S P2 P1
      (ctx.hypothesisTwo.swap_of_commutator_ne_bot S0 S P1 P2 hGa)

/-- **Stellmacher (8.3).** Centrality of the next vertex module forces
noncontainment of the initial residual's two-core in the next vertex core. -/
public theorem lemma_eight_three
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤
      QAt ctx.Γ ctx.criticalPath.firstStep := by
  intro hcontained
  obtain ⟨hcomm,hZaT⟩ := eight_three_core_bound_data ctx hcontained
  have hcore := eight_three_core_eq_center ctx hcenter hcomm
  exact baumann_not_le_next ctx
    (eight_three_action_comparison ctx hcore (hcore.le.trans hZaT))

end Stellmacher.SectionEight
