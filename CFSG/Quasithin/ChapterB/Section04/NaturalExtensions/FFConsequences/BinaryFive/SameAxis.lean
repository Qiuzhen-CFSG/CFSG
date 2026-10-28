module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Bounds
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Propagation
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Placement
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Generation

/-!
# Assembly of the same-orientation four-group argument

The geometric placement and both literal normalizer-generation claims give
an ambient quadratic axis four-group, including the difficult rank-four case
where none lies in the offender. In that case the first generation statement
shows that the radical fixes the displacements of the order-two intersection;
the second propagates this to quadraticity of the whole radical. The witness
has a common codimension-one fixed space on the original quotient.

Thompson replacement then supplies the four-group for every best offender
inside the given Sylow subgroup. The splitting consumer retains only the
exact B.4.9(1) implication as a parent-supplied premise; all same-orientation
geometric premises are discharged here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9, final paragraph on printed p.95.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
open QuasisimpleSource BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)

/-- The group-geometric inputs feed the actual upstairs action calculation.
No quadraticity premise is imposed on the ambient radical. -/
theorem axisFour_of_placement_and_generation {B : Subgroup G}
    (hq : IsQuadratic ρ B) (hp : PlacementAlternative d hF B)
    (hg : ∀ W H, RankFourPosition d hF B W H →
      NormalizerGeneration B (B ⊓ markedRadical d hF H) (markedRadical d hF W)) :
    HasQuadraticAxisFour d := by
  rcases hp with ⟨E, hEB, hE⟩ | ⟨W, H, hpos, E, hER, hE⟩
  · exact ⟨E, hE, fun a ha b hb v => hq a (hEB ha) b (hEB hb) v⟩
  · exact axisFour_of_normalizer_generation ρ d hq inf_le_left (hg W H hpos) hER hE

variable [FiniteDimensional (ZMod 2) V]

/-- Conditional consumer on the original Sylow subgroup, retained for the
separate placement and generation interfaces. `splits_of_bestOffender`
below discharges both geometric premises. -/
theorem splits_of_placement_and_generation
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    (T : Sylow 2 G)
    (splitting : ∀ d' : DoubleNatural F 5 ρ,
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (placement : ∀ B : Subgroup G, B ≤ (T : Subgroup G) →
      IsMinimalBestOffender ρ B → IsQuadratic ρ B →
      PlacementAlternative d hF B)
    (generation : ∀ (B : Subgroup G) W H, RankFourPosition d hF B W H →
      NormalizerGeneration B (B ⊓ markedRadical d hF H) (markedRadical d hF W))
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G)) (hA : IsBestOffender ρ A) :
    d.Splits := by
  apply splits_of_axisFour d hF splitting
  apply axisFour_of_minimal_witnesses d T _ hAT hA
  intro B hBT hB hq
  by_cases hr : rank B ≤ 3
  · exact axisFour_of_rank_le_three d hF e (hB.1.isOffender ρ) hq hr
  · exact axisFour_of_placement_and_generation d hF hq
      (placement B hBT hB hq) (generation B)

include hF in
/-- The same-orientation four-group construction required by B.4.9(2)(i).
The witness lies in the original group and is quadratic on the extension;
its three nonidentity elements have the same hyperplane as their exact fixed
space on the literal quotient. No splitting hypothesis is used. -/
theorem axisFour_of_minimalBestOffender
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    (T : Sylow 2 G) {B : Subgroup G} (hBT : B ≤ (T : Subgroup G))
    (hB : IsMinimalBestOffender ρ B) (hq : IsQuadratic ρ B) :
    HasQuadraticAxisFour d := by
  exact axisFour_of_placement_and_generation d hF hq
    (placement d hF e T hBT hB hq)
    (fun _ _ hpos => normalizerGeneration_of_rankFourPosition d hF hpos)

include hF in
/-- B.4.9(2)(i) in dimension five with isomorphic natural factors, conditional
only on the exact B.4.9(1) implication. Replacement and the completed geometry
discharge its common-axis four-group and upstairs quadraticity requirements. -/
theorem splits_of_bestOffender
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    (T : Sylow 2 G)
    (splitting : ∀ d' : DoubleNatural F 5 ρ,
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G)) (hA : IsBestOffender ρ A) :
    d.Splits := by
  apply splits_of_axisFour d hF splitting
  exact axisFour_of_minimal_witnesses d T
    (fun _ hBT hB hq => axisFour_of_minimalBestOffender d hF e T hBT hB hq) hAT hA

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
