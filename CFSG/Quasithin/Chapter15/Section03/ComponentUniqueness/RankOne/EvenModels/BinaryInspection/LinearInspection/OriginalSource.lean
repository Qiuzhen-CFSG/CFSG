module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FiveExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.MiddleMarking
public import Theory.SpecificGroups.SymmetricEight.PairFlagParabolic

/-!
# The original binary four-dimensional component branch

The actual component intersection contains a Sylow two-subgroup and has
solvable three-residual, with three-part of order three. Intrinsic flag
recognition therefore identifies it as a single-node parabolic. Maximality
among Sylow-invariant overgroups supplies an outer automorphism preserving
that parabolic, so its node must be the middle one. The simultaneous A₈
comparison then contradicts the original normal four-group.

All placements use the reduced configuration's actual quotient images.
No containment of the involution centralizer in M is assumed.

Source: Aschbacher--Smith, 15.3.43, printed p.1140; the binary parabolic
recognition argument also occurs in 15.3.28, printed pp.1130--1132.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

/-- The original configuration itself selects the binary middle node and
an outer Sylow element, without a global centralizer containment. -/
theorem middle_node_of_original_configuration (hs : IsSimpleGroup L)
    (iso : ClassicalGroup.IsPSL L 4 2) : Nonempty (MiddleNodeData c) := by
  obtain ⟨e⟩ := exists_component_linearEquiv c hs (by decide : 0 < 4) iso
  obtain ⟨U, hU⟩ := FiveExclusion.exists_modelSylow c e
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer U
  obtain ⟨i, hi⟩ :=
    CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.BinaryHigher.FlagRecognition.four
      U b hb (FiveExclusion.intersection c e)
      (hU ▸ FiveExclusion.sylowIntersection_le_intersection c e)
      (FiveExclusion.intersection_ne_top c e)
      (FiveExclusion.intersection_residual_solvable c e hs)
      (FiveExclusion.intersection_three_dvd c e hs)
      (FiveExclusion.intersection_three_subgroup_bound c e hs)
  have hout := FiveExclusion.outer_of_minimalParabolic c (by decide : 3 ≤ 3) e b i hi
  obtain ⟨a, ha, hP⟩ := FiveExclusion.exists_outer_preserving c e hout
  rw [hi] at hP
  have hnode := outer_preserves_minimalParabolic_middle (by decide : 2 ≤ 3)
    (by decide : 3 ≤ 4) b i a ha hP
  have hi1 : i = 1 := Fin.ext (by simpa using (by omega : i.val = 1))
  rw [hi1] at hi
  exact ⟨⟨e, b, hi, hout⟩⟩

/-- The original normal four-group excludes the PSL₄(2) component. -/
theorem not_linear_four_of_original_configuration (hs : IsSimpleGroup L)
    (iso : ClassicalGroup.IsPSL L 4 2) : False := by
  obtain ⟨h⟩ := middle_node_of_original_configuration c hs iso
  obtain ⟨e, b, hpair, _⟩ :=
    Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.simultaneous_comparison
  exact false_of_middle_node_comparison c h e b hpair

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
