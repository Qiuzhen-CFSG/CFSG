module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization

/-!
# Reorienting the ambient (9.8) statement

A proof of the normalized ambient bound transfers to any commuting critical
pair with a prescribed next vertex on a shortest path. The ambient group,
embedding and Hypothesis Two remain unchanged; one conjugator transports
all three vertices. The bound is an explicit premise, not an admission.

This supports the interchange of the first-step and terminal roles in the
opening of (9.9), printed p.56 / PDF p.46 of the full scan. The caller must
still prove criticality, adjacency, the distance identity and commutation.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem nine_eight_critical_pair_of_ambient_bound
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (left right next : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hadj : ctx.Γ.adjacent left next)
    (hdistance : ctx.Γ.distance left right = ctx.Γ.distance next right + 1)
    (hcomm : ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ = ⊥)
    (hcontain : ZAt ctx.Γ right ≤ VAt ctx.Γ next) :
    ctx.criticalPath.length ≤ 3 := by
  obtain ⟨actor, path, hleft, hright, hnext, hlength⟩ :=
    exists_criticalPath_of_critical_pair_through_neighbor ctx.sectionSeven
      ctx.Γ ctx.criticalPath left right next hcritical hadj hdistance
  have hpathComm : ⁅ctx.Γ.z path.a, ctx.Γ.z path.a'⁆ = ⊥ := by
    rw [hleft, hright, z_act, z_act, ← Subgroup.map_commutator]
    change (⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆).map _ = ⊥
    rw [hcomm, Subgroup.map_bot]
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    { ctx with criticalPath := path, commutator_eq := hpathComm }
  have hpathContain : ZAt ctx.Γ path.a' ≤ VAt ctx.Γ path.firstStep := by
    change z ctx.Γ path.a' ≤ v ctx.Γ path.firstStep
    rw [hright, hnext, z_act, v_act]
    exact Subgroup.map_mono hcontain
  have hbound := bound shifted hpathContain
  change path.length ≤ 3 at hbound
  rwa [hlength] at hbound

end Stellmacher.SectionNine
