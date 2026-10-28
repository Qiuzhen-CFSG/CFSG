module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.EarlierGeometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted

/-!
# The tensor complement intersection in 14.4.10

The natural and deleted constituent calculations prove the complement
intersection bound for both source actor groups. Their geometric producers
derive the component intersection from the actual elementary order-eight
actor, Sylow subgroup and relative normality, preserving the supplied form.

The common reduction identifies the intersection with the line on the cubic
translate of the source point. Applying the appropriate calculation to the
canonical form gives the literal displayed inequality. The earlier bound
[Wᵍ,W] ≤ E and the existing central-kernel lift then give X₁ ∈ Y.

Only the authorized selected constituent and component marking remain explicit;
their construction belongs to the source assembly owner. No normalization,
actor-placement or finite-calculation premise remains.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.1010.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Both concrete constituent alternatives satisfy the finite complement
calculation for either source actor group. -/
theorem source_complement_intersection (hcase : D = ⊤ ∨ D = AltFive)
    {σ : Representation (ZMod 2) D V} (hmodel : IsSourceConstituent hAD σ) :
    ComplementIntersectionCalculation σ := by
  rcases hmodel with hnatural | hdeleted
  · exact natural_complement_intersection hcase hnatural
  · exact deleted_complement_intersection hcase hdeleted

namespace CaseFiveCoordinates
variable {G : Type*} [Group G] [Finite G] {H U : Subgroup G}
  (c : CaseFiveCoordinates hAD (V := V) H U)

/-- The first inequality displayed in the proof of 14.4.10, for both actual
constituent models and the specified cubic-translate complement. -/
theorem EarlierGeometry.intersection
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) :=
  h.intersection_of_calculation c B s hK
    (source_complement_intersection c.actor_case c.constituent_model)

/-- The literal source commutator bound and extraspecial central-kernel lift
give X₁ ∈ Y in both constituent alternatives. -/
theorem EarlierGeometry.first_mem_Y [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    first H ∈ YFamily H T P (intersectionLayer U P g) :=
  h.first_mem_Y_of_intersection c s (h.intersection c B s hK)

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
