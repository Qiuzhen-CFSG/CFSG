module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfSylow

/-!
# The independent outside-conjugate source obligation

The 10.2.10 argument may take N_G(L)≤M explicitly while the existing
half-Sylow uniqueness owner proves 10.2.6. The adapter here discharges that
premise from its exact published contract. Thus the intersection and
normalizer producers can proceed independently, and final assembly retains
both dependencies. Neither earlier source theorem is asserted here.
Source: Aschbacher--Smith 10.2.6(2), 10.2.10(1) and 10.1.3, pp.742,749,753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Earlier source geometry, conditional only on the independent component
normalizer bound. The fusion branch avoids unnecessary residual calculations. -/
def IntersectionsOfNormalizersAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    Context D → normalizer (L : Set G) ≤ D.maximalLocal →
    FusionCase D ∨ IntersectionInputs D

/-- The existing half-Sylow owner supplies exactly the retained earlier premise. -/
theorem intersectionsAt_of_halfSylowUnique
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hi : IntersectionsOfNormalizersAt T) : IntersectionsAt T := by
  intro L D c
  apply hi L D c
  exact PointControl.component_normalizer_le_of_halfSylowUnique D c.nonnormal
    (hhalf c.many L D c.nonnormal c.notA5)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
