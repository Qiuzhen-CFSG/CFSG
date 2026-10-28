module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourSeven
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourPlaneOrbit
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FourMixedPlane
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FivePlane

/-!
# Local control in both natural-module degrees

The original abelian point span supplies point-component escape, both
centralizer bounds, the actual point models, and plane movement. The A₇
row is impossible by the placed quadratic actor; the two binary point
rows use their proved plane bounds. Thus every clause of 12.9.5--7 holds
on the same original flag, in degrees four and five.

The remaining nonabelian elimination and corrected catalogue are separate
obligations of the NaturalSource assembly. Source: Aschbacher--Smith,
12.9.5--7, refs/quasithin.pdf, printed pp.860--862.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u

/-- The complete local-control conclusion on the original abelian point span,
in both source degrees. The A₇ row is excluded by its actual quadratic actor. -/
theorem localControl_of_abelian
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) :
    LocalControl C := by
  rcases hn with rfl | rfl
  · rcases point_models_of_abelian h (Or.inl rfl) earlier F hab C with hm | hm | hm
    · exact (four_seven_abelian_impossible h earlier F hab C hm).elim
    · exact four_localControl_of_binary_four h earlier F hab C hm
    · exact four_localControl_of_binary_five h earlier F hab C hm
  · exact five_localControl_of_abelian h earlier F hab C

/-- Source 12.9.5--7 with all local-control premises discharged, retaining
only the abelianity and component inputs of the original stage contract. -/
theorem localControlInput : LocalControlInput KnownSimple.IsKnownSimple.{u} := by
  intro X _ _ T L V n h hn _ earlier F hab C
  exact localControl_of_abelian h hn earlier F hab C

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
