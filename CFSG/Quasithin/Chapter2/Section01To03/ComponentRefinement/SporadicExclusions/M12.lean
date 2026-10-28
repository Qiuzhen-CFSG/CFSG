module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M12.Reduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M12.Transport
public import Theory.Mathieu.M12.BlockGeometry
public import Theory.Mathieu.M12.BlockGeometry.SecondSquareControl

/-!
# The second-parabolic block obstruction for M₁₂

The actual marked second parabolic has a normal abelian two-subgroup whose
squares detect its natural-four action. Its square centralizer is a two-group.
The general subnormal-core argument therefore excludes all short subnormal
blocks from any normal section cover by these full parabolics, including
central two-kernels and two-group permutations of component factors.

This supplies the block-obstruction part of Aschbacher–Smith 2.3.9(7),
printed p.526. The conditional constructor records the reduction from an
ambient section cover, while the final theorem below discharges that geometry
using the invariant M₁₂ model and its central-cover/component-orbit transport.
The final contradiction and seven-case assembly belong to the parent
sporadic-exclusion module.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M12Exclusion
open Theory.GroupTheory Sporadic.Mathieu.M12SmallPair

/-- The concrete M₁₂ parabolic supplies the square obstruction without any
extra intrinsic module or subgroup-calculation premise. -/
theorem not_short_of_parabolicCover {K : Type*} [Group K] [Finite K]
    (c : NormalPowerCover 2 K secondParabolic) (B : Subgroup K)
    (hB : B.IsSubnormal) : ¬ ChapterC.IsShort B :=
  not_short_of_normalPowerCover SecondSquareControl.control c B hB

/-- Conditional cover assembly from an already transported local geometry. -/
theorem nonempty_centralizerBlockCover_of_localGeometry
    {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m12)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) :=
  ⟨centralizerBlockCover_of_geometry SecondSquareControl.control h d g⟩

/-- The M₁₂ local block cover obtained from the invariant model geometry and
the actual central-cover/component-orbit transport. -/
theorem nonempty_centralizerBlockCover
    {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m12) :
    Nonempty (CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z) := by
  obtain ⟨g⟩ := localGeometry_of_intrinsicGeometry
    Sporadic.Mathieu.M12SmallPair.BlockGeometry.geometry h d
  exact nonempty_centralizerBlockCover_of_localGeometry h d g

end CFSG.Quasithin.Chapter2.ComponentRefinement.M12Exclusion
