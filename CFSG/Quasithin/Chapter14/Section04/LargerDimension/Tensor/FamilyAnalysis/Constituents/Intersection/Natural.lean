module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Calculation
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.PointRoot
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Actors

/-!
# Source applications of the natural complement calculation

The trace-determinant calculation handles both the full root group and an
order-two component intersection with an outer field actor. It uses the
given canonical form, component marking and selected constituent.

Point/root normalization constructs an equivariant frame from the actual
nonzero tensor point and elementary actor. The actor dichotomy then supplies
either the full marked root group or an outer actor with Frobenius action in
that same frame. These discharge both geometric premises of the calculation,
for D = A₅ and D = S₅ and every extension of the given natural A₅ action.

The source applications retain the authorized selected constituent and
component marking on the actual quotient maps. They require no additional
normalization, actor placement or invariant-form premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.4.10, first proof paragraph, printed p.1010.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The natural calculation, conditional on the two geometric producers. -/
theorem natural_complement_intersection_of_normalization
    {σ : Representation (ZMod 2) D V} (hnatural : IsNaturalFour hAD σ)
    (hpoint : Natural.Intersection.PointRootNormalization hAD σ)
    (hactor : Natural.Intersection.ActorNormalization hAD σ) :
    ComplementIntersectionCalculation σ :=
  Natural.Intersection.calculation_of_normalization hnatural hpoint hactor

/-- The natural branch of the finite complement calculation, including both
source overgroups and every extension of the given natural A₅ action. -/
theorem natural_complement_intersection (hcase : D = ⊤ ∨ D = AltFive)
    {σ : Representation (ZMod 2) D V} (hnatural : IsNaturalFour hAD σ) :
    ComplementIntersectionCalculation σ :=
  natural_complement_intersection_of_normalization hnatural
    (Natural.Intersection.point_root_normalization hAD hcase σ)
    (Natural.Intersection.actor_normalization hAD hcase σ)

namespace CaseFiveCoordinates
variable {G : Type*} [Group G] [Finite G] {H U : Subgroup G}
  (c : CaseFiveCoordinates hAD (V := V) H U)

/-- The calculation gives the literal source intersection for the selected constituent. -/
theorem EarlierGeometry.natural_intersection_of_normalization
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hnatural : IsNaturalFour hAD c.constituent)
    (hpoint : Natural.Intersection.PointRootNormalization hAD c.constituent)
    (hactor : Natural.Intersection.ActorNormalization hAD c.constituent) :
    c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) :=
  h.intersection_of_calculation c B s hK
    (natural_complement_intersection_of_normalization hnatural hpoint hactor)

/-- The same finite calculation gives the actual Y-family membership through the lift. -/
theorem EarlierGeometry.natural_first_mem_Y_of_normalization [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hnatural : IsNaturalFour hAD c.constituent)
    (hpoint : Natural.Intersection.PointRootNormalization hAD c.constituent)
    (hactor : Natural.Intersection.ActorNormalization hAD c.constituent) :
    first H ∈ YFamily H T P (intersectionLayer U P g) :=
  h.first_mem_Y_of_calculation c B s hK
    (natural_complement_intersection_of_normalization hnatural hpoint hactor)

/-- The natural-module inequality displayed in the first proof paragraph
of 14.4.10, on the actual source quotient and selected complement. -/
theorem EarlierGeometry.natural_intersection
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hnatural : IsNaturalFour hAD c.constituent) :
    c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) :=
  h.intersection_of_calculation c B s hK
    (natural_complement_intersection c.actor_case hnatural)

/-- In the natural branch the earlier source commutator bound and central
kernel lift give X₁ ∈ Y, with no extra finite-calculation premise. -/
theorem EarlierGeometry.natural_first_mem_Y [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hnatural : IsNaturalFour hAD c.constituent) :
    first H ∈ YFamily H T P (intersectionLayer U P g) :=
  h.first_mem_Y_of_calculation c B s hK
    (natural_complement_intersection c.actor_case hnatural)

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
end
