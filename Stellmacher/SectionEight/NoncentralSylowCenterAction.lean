module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.Result7_3
public import Stellmacher.SectionFiveToSeven.Result7_4
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven

/-!
# Noncentral centers force the two Sylow omega actions

Under the actual hypotheses of Stellmacher (8.2), neither distinguished
edge stabilizer centralizes the omega-center of the common Sylow subgroup.
This supplies the nontrivial-commutator inputs for (6.3), without invoking
that later result; the source is Journal of Algebra 190 (1997), p.37.

If a stabilizer centralizes the Sylow omega-center, that subgroup is normal
there. The normal-omega consequence of (7.3) identifies its conjugate join
with the vertex center, which is then central. Critical endpoint
noncommutation rules this out at the initial vertex, and the explicit
(8.2) hypothesis rules it out at the next vertex. The critical-edge
identification then yields the claims for both original local groups.

The supplemental theorem uses `SectionEightLocalContext` and its genuine
Section Seven hypotheses. The original public theorem remains a wrapper
through `SectionEightContext.toLocalContext`, preserving the graph and
critical path definitionally. No additional Sylow hypothesis is imposed
on the ambient group of the supplemental theorem.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem noncentral_z_sylow_action
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    (d : Γ.Vertex) (hS : IsSylowTwoIn S (stabilizer Γ d))
    (hn : ¬ z Γ d ≤ CenterAmbient (stabilizer Γ d)) :
    ⁅stabilizer Γ d, omegaOneCenter S⁆ ≠ ⊥ := by
  intro hc
  have hC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hΩS : omegaOneCenter S ≤ S :=
    (SevenSix.omegaOneCenter_le_centerAmbient S).trans (Subgroup.map_subtype_le _)
  have hΩP := hΩS.trans hS.1
  have hnormal : NormalIn (omegaOneCenter S) (stabilizer Γ d) := by
    refine ⟨hΩP, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hΩP).mpr
      (hC.trans (Subgroup.centralizer_le_normalizer _))
  apply hn
  rw [z_eq_omega_sylow_of_normal Γ d hS hnormal]
  intro x hx
  refine ⟨⟨x, hΩP hx⟩, ?_, rfl⟩
  change (⟨x, hΩP hx⟩ : stabilizer Γ d) ∈ Subgroup.center (stabilizer Γ d)
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp (hC y.property) x hx).symm

public theorem eight_two_noncentral_sylow_center_action_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ⁅P1, omegaOneCenter S⁆ ≠ ⊥ ∧ ⁅P2, omegaOneCenter S⁆ ≠ ⊥ := by
  let h := ctx.sectionSeven
  have h74 := lemma_seven_four h ctx.Γ ctx.criticalPath
  have ha : ¬ z ctx.Γ ctx.criticalPath.a ≤
      CenterAmbient (stabilizer ctx.Γ ctx.criticalPath.a) := by
    intro hc
    apply ctx.commutator_ne
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact hc.trans ((SevenSix.centerAmbient_le_centralizer _).trans
      (Subgroup.centralizer_le h74.reverse_containment.1))
  have hs := SevenSix.edge_sylow_data h ctx.Γ ctx.criticalPath
  have hleft := noncentral_z_sylow_action ctx.Γ _ hs.1 ha
  have hright := noncentral_z_sylow_action ctx.Γ _ hs.2 hcenter
  rcases ctx.criticalPath.edge_stabilizers_are_P with he | he
  · rw [he.1] at hleft
    rw [he.2] at hright
    exact ⟨hleft, hright⟩
  · rw [he.1] at hleft
    rw [he.2] at hright
    exact ⟨hright, hleft⟩

public theorem eight_two_noncentral_sylow_center_action
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ⁅P1, omegaOneCenter S⁆ ≠ ⊥ ∧ ⁅P2, omegaOneCenter S⁆ ≠ ⊥ :=
  eight_two_noncentral_sylow_center_action_local ctx.toLocalContext hcenter

end Stellmacher.SectionEight
