module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FourNode.Flag
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FourNode.Endpoints

/-!
# The actual outer middle node in binary degree four

The source inner involution constructs a transvection centralizer containing
the component Sylow. Its proper overgroups lie in the line or hyperplane
parabolic. The cubic residual excludes equality with either endpoint. An
inner Sylow action would make an endpoint invariant, contradicting the given
invariant maximality. An outer Sylow element instead reverses the full flag,
forcing the local intersection to be the middle minimal parabolic.

The result records the actual component equivalence, basis and literal image
of M ∩ L. The later S₈ comparison and permutation markings are separate.

Source: Aschbacher--Smith, 15.3.43, n = 1 paragraph, printed p.1140;
1.1.5(3)(a), p.501; A.2.3--4, p.33.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- In binary degree four, the maximal invariant component parabolic is the
actual middle minimal parabolic, and the Sylow image has an outer element. -/
theorem middle_node_of_parabolic (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (hz : SourceInvolution S M z) (hs : IsSimpleGroup L)
    (iso : ClassicalGroup.IsPSL L 4 2) (hi : ActsInner L z)
    (hp : ParabolicInspection.QuotientParabolic c) : Nonempty (MiddleNodeData c) := by
  obtain ⟨h⟩ := fourFlagData_of_source c hz hs iso hi
  exact middle_node_of_flag_and_endpoint_exclusion c hp h
    (four_endpoint_excluded c hs h.linear h.basis)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
