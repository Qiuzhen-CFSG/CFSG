module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Actors.Extension
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Natural.Calculation

/-!
# The natural tensor actor dichotomy

Every supplied point/root frame has one of the two actor configurations needed
in the natural complement calculation. The elementary actor either contains
the full marked upper root group, or contains a pure outer actor. In the latter
case its actual extending action is an upper root followed by Frobenius in the
same vector marking. The proof does not choose an unrelated S₅ extension.

The application to the complement calculation discharges actor normalization;
construction of the point/root frame remains the sole explicit geometric input.
This is a prerequisite for the finite calculation in the first proof paragraph
of Aschbacher–Smith 14.4.10, printed p.1010 (combined manuscript, 1 March 2004),
using the tensor models of 14.4.2(5), printed p.1006.
-/

public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
variable {D : Subgroup Five} {V : Type*} [AddCommGroup V] [Module Bit V]

/-- The actor alternatives hold in every genuine supplied point/root frame. -/
theorem actor_normalization (hAD : AltFive ≤ D) (_hcase : D = ⊤ ∨ D = AltFive)
    (σ : Representation Bit D V) : ActorNormalization hAD σ := by
  intro d p
  rcases p.root_or_outer d with hroot | ⟨a, ha, houter⟩
  · exact Or.inl hroot
  · obtain ⟨b, hb⟩ := p.outer_action d ha houter
    exact Or.inr ⟨a, b, ha, hb⟩

/-- The actual natural complement calculation, with only frame construction
left to the independent point/root normalization producer. -/
theorem calculation_of_pointNormalization (hAD : AltFive ≤ D)
    (hcase : D = ⊤ ∨ D = AltFive) {σ : Representation Bit D V}
    (hnatural : IsNaturalFour hAD σ) (hpoint : PointRootNormalization hAD σ) :
    ComplementIntersectionCalculation σ :=
  calculation_of_normalization hnatural hpoint (actor_normalization hAD hcase σ)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Intersection
