module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.LateSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.LatePoint

/-!
# The classified moved space is the terminal point space

Restriction to the late actor preserves the literal component commutator.
The commutator-span and coinvariant-kernel definitions agree generator by
generator, so the terminal point's subrepresentation equals the one in
every B.5.1 moved-section witness. Rewriting by this equality retains both
the original vectors and their literal fixed-space quotients.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99–103, and the point paragraphs of 15.3.49 on p.1145.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
open ReducedModels ComponentReduction ModelReduction BinaryModels ModelExclusions

private theorem moved_eq_ker {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (A : Subgroup D) :
    moved ρ A = Coinvariants.ker (ρ.comp A.subtype) := by
  unfold moved subspaceCommutator Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, v, _, rfl⟩
    exact ⟨(⟨a, ha⟩, v), rfl⟩
  · rintro ⟨⟨a, v⟩, rfl⟩
    exact ⟨a, a.property, v, Submodule.mem_top, rfl⟩

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    {r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper}

/-- Every classified late moved space is the literal space of the terminal point. -/
theorem point_space_eq (p : TerminalPoint r)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (c : MovedSection
      (r.placed.action.representation.comp (lateActor r.placed.action).subtype)
      ((starImage H L).subgroupOf (lateActor r.placed.action))) :
    PointOnLateActor.space p = c.space := by
  apply Subrepresentation.ext
  change p.space.toSubmodule = c.space.toSubmodule
  rw [c.space_eq]
  exact p.component_space.trans ((moved_eq_ker _ _).symm.trans
    (NaturalSelection.moved_subgroupOf (r.component_le_late_actor sections orbits)).symm)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
