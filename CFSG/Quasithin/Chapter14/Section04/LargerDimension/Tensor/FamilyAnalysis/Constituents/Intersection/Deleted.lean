module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.Calculation
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.ActorGenerators
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.PointNormalization

/-!
# The deleted-module complement intersection and its source applications

The A₅ identification intertwines the entire D-action. Sylow fixation gives
weight-four point coordinates, and relative normality in the full point
centralizer puts both marked double transpositions in the actual actor.
Two successive displacements then give the cubic translate of the point.
Invariance of the supplied bilinear form makes the intermediate displacement
perpendicular to the point, for that same form without a coordinate-form
assumption. This proves the deleted calculation for both D = A₅ and D = S₅,
with no remaining point-normalization or actor-placement premise.

The source application uses the authorized selected constituent and component
marking on the actual quotient maps. Source: Aschbacher–Smith, combined
manuscript of 1 March 2004, 14.4.10, first proof paragraph, printed p.1010.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The exact calculation, conditional only on the two geometric producers. -/
theorem deleted_complement_intersection_of_normalization
    {σ : Representation (ZMod 2) D V} (hdeleted : IsDeletedFour hAD σ)
    (hpoint : Deleted.PointNormalization σ) (hactor : Deleted.ActorGenerators hAD σ) :
    ComplementIntersectionCalculation σ :=
  Deleted.calculation_of_actorPlacement hdeleted
    (Deleted.actorPlacement_of_normalization hpoint hactor)

/-- The deleted branch of the finite complement calculation, including both
source overgroups and every extension of the given A₅ action. -/
theorem deleted_complement_intersection (hcase : D = ⊤ ∨ D = AltFive)
    {σ : Representation (ZMod 2) D V} (hdeleted : IsDeletedFour hAD σ) :
    ComplementIntersectionCalculation σ :=
  deleted_complement_intersection_of_normalization hdeleted
    (Deleted.point_normalization hAD hcase σ)
    (Deleted.actor_generators hAD hcase σ)

namespace CaseFiveCoordinates
variable {G : Type*} [Group G] [Finite G] {H U : Subgroup G}
  (c : CaseFiveCoordinates hAD (V := V) H U)

/-- The normalized deleted calculation gives the actual source intersection. -/
theorem EarlierGeometry.deleted_intersection_of_normalization
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hdeleted : IsDeletedFour hAD c.constituent)
    (hpoint : Deleted.PointNormalization c.constituent)
    (hactor : Deleted.ActorGenerators hAD c.constituent) :
    c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) :=
  h.intersection_of_calculation c B s hK
    (deleted_complement_intersection_of_normalization hdeleted hpoint hactor)

/-- The corresponding literal Y-family conclusion, through the existing lift. -/
theorem EarlierGeometry.deleted_first_mem_Y_of_normalization [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hdeleted : IsDeletedFour hAD c.constituent)
    (hpoint : Deleted.PointNormalization c.constituent)
    (hactor : Deleted.ActorGenerators hAD c.constituent) :
    first H ∈ YFamily H T P (intersectionLayer U P g) :=
  h.first_mem_Y_of_calculation c B s hK
    (deleted_complement_intersection_of_normalization hdeleted hpoint hactor)

/-- The deleted-module inequality displayed in the first proof paragraph
of 14.4.10, on the actual source quotient and selected complement. -/
theorem EarlierGeometry.deleted_intersection
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hdeleted : IsDeletedFour hAD c.constituent) :
    c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) :=
  h.intersection_of_calculation c B s hK
    (deleted_complement_intersection c.actor_case hdeleted)

/-- In the deleted branch the earlier source commutator bound and central
kernel lift give X₁ ∈ Y, with no extra finite-calculation premise. -/
theorem EarlierGeometry.deleted_first_mem_Y [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hdeleted : IsDeletedFour hAD c.constituent) :
    first H ∈ YFamily H T P (intersectionLayer U P g) :=
  h.first_mem_Y_of_calculation c B s hK
    (deleted_complement_intersection c.actor_case hdeleted)

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
