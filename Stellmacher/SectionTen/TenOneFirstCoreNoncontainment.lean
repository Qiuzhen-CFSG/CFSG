module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Stellmacher.ResidualCoreCommutator
public import Stellmacher.SectionFiveToSeven.LocalResidualCoreContainment

/-!
# The residual-core noncontainment in the proof of Stellmacher (10.1)

In the actual ambient Section Ten geometry, the first-step residual two-core
is not contained in its elementary neighbor module. The transported (7.6)(b)
noncontainment makes that residual core escape the middle two-core, while
critical distance three puts the first-step module inside the middle core.
The assumed containment would contradict those two facts.

The local residual has odd-order quotient over its two-core, and equals its
own two-residual. The residual-core commutator theorem therefore says
`[O₂(E),E]=O₂(E)`, yielding noncentral action modulo the module as well.

This establishes the first implication leading to assertion (3) on printed
p.60/PDF p.50 of `refs/files/stellmacher-n-group.pdf`. It does not assert a
chief-factor conclusion; that further action-theoretic inference is separate.
The final wrapper retains the original single-carrier Section Ten interface.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The first residual two-core is not contained in its neighbor module,
as used in assertion (3). -/
public theorem ten_one_first_core_not_le_module
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  obtain ⟨_, hadj, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hescape := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.firstStep middle
    ⟨1, ctx.Γ.act_one _⟩ (ctx.Γ.adjacent_symm hadj)
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hmodule : VAt ctx.Γ ctx.criticalPath.firstStep ≤ QAt ctx.Γ middle :=
    (show VAt ctx.Γ ctx.criticalPath.firstStep ≤ GeneratedNeighborhoodV ctx.Γ middle from
      le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle)
  exact fun hle => hescape (hle.trans hmodule)

/-- The first residual acts nontrivially on its two-core modulo the neighbor module. -/
public theorem ten_one_first_core_action_not_le_module
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ¬ ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep),
        EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let E := EAt ctx.Γ ctx.criticalPath.firstStep
  have hE : E = twoResidualIn P := by
    change ctx.Γ.twoResidualAt ctx.criticalPath.firstStep = _
    rw [ctx.Γ.twoResidualAt_def]
    rfl
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm
        ctx.criticalPath.firstStep_adj)) P le_rfl
  have hcore : twoCoreIn E = ⁅twoCoreIn E, E⁆ := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect
        hperfect hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh
  rw [← hcore]
  exact ten_one_first_core_not_le_module ctx middle hpath

public theorem ten_one_first_core_not_le_module_legacy
    (ctx : SectionTenContext H S0 S P1 P2)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep :=
  ten_one_first_core_not_le_module ctx.toAmbientContext middle hpath
public theorem ten_one_first_core_action_not_le_module_legacy
    (ctx : SectionTenContext H S0 S P1 P2)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    ¬ ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep),
        EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep :=
  ten_one_first_core_action_not_le_module ctx.toAmbientContext middle hpath
end Stellmacher.SectionTen
