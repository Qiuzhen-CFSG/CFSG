module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Contracts
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Bounds
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Parabolics
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.DualGeometry.RankFour
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.DualGeometry.HighRank
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.DualGeometry.Levi
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive

/-!
# Dual dimension-five extensions: quadratic axes and parabolic alternatives

Thompson replacement gives a quadratic minimal best offender inside the given
Sylow subgroup. Its rank is four, five or six. The two-cost construction in
rank four and the quadratic displacement construction in higher ranks each
give an actual common-axis four-group on the literal quotient, quadratic on
the original extension. Only then is the exact B.4.9(1) implication applied.

The original rank-four offender lies in the genuine end-node Levi supplied
by complementary four- and one-spaces; higher ranks lie in an interior
parabolic's intrinsic two-core. These placements use the original coherent
marking and require no splitting. Splitting supplies the exact ratio 5/6.
Thus the dual B.4.9(2)(i),(iv) application retains only the B.4.9(1) implication
as its earlier-source premise, for discharge by the final source assembly.
Source: Aschbacher–Smith, printed pp.94–95, combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {F : BinaryField} {ρ : Representation (ZMod 2) G V}

/-- Every quadratic dual best offender contains a common-axis four-group
on the original quotient, still quadratic upstairs. This covers all three
replacement ranks before applying the splitting implication. -/
theorem dual_quadratic_axis (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {B : Subgroup G} (hB : IsBestOffender ρ B) (hq : IsQuadratic ρ B) :
    ∃ E : Subgroup G, E ≤ B ∧ QuadraticSplitting.IsAxisFour d E ∧ IsQuadratic ρ E := by
  rcases dual_rank_cases d hF e (hB.isOffender ρ) with hr | hr | hr
  · exact dual_rank_four_axis d hF e hB hr
  · exact high_rank_quadratic_axis d hF hB.1 (by omega) hq
  · exact high_rank_quadratic_axis d hF hB.1 (by omega) hq

/-- The dual geometry input for the replacement consumer. The construction
works for every minimal best offender, hence in particular for those in the
source's specified Sylow subgroup. No splitting premise is used. -/
theorem dual_hasQuadraticAxisFour (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {B : Subgroup G} (hB : IsMinimalBestOffender ρ B) (hq : IsQuadratic ρ B) :
    HasQuadraticAxisFour d := by
  obtain ⟨E, _, hE, hqE⟩ := dual_quadratic_axis d hF e hB.1 hq
  exact ⟨E, hE, hqE⟩

/-- The rank-four dual branch splits and has ratio 5/6. The only additional
premise is the exact source B.4.9(1) implication, before the final assembly. -/
theorem dual_rank_four_splits_and_ratio (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (splitting : ∀ d' : DoubleNatural F 5 ρ,
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hr : rank A = 4) :
    d.Splits ∧ quadraticRatio ρ = 5 / 6 := by
  obtain ⟨E, _, hE, hq⟩ := dual_rank_four_axis d hF e hA hr
  have hs := splits_of_axisFour d hF splitting ⟨E, hE, hq⟩
  exact ⟨hs, dual_ratio_of_splits d hF e hs⟩

/-- The dual-orientation B.4.9(2)(i),(iv) application on the actual Sylow
offender. Both geometric inputs are discharged: replacement constructs the
quadratic axis, and the original offender has the full parabolic placement.
Only the exact earlier-source B.4.9(1) implication remains explicit. -/
theorem dual_ff (d : DoubleNatural F 5 ρ) (hF : F.degree = 1) (T : Sylow 2 G)
    (splitting : ∀ d' : DoubleNatural F 5 ρ,
      QuadraticSplitting.SourceHypotheses d' → d'.Splits)
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G)) (hA : IsBestOffender ρ A) :
    d.Splits ∧ quadraticRatio ρ = 5 / 6 ∧ DualAlternatives d hF A := by
  have haxis := axisFour_of_minimal_witnesses d T
    (fun _ _ hB hq => dual_hasQuadraticAxisFour d hF e hB hq) hAT hA
  have hs := splits_of_axisFour d hF splitting haxis
  exact ⟨hs, dual_ratio_of_splits d hF e hs,
    dual_alternatives_of_rank_four d hF e hA
      (dual_rank_four_endNodePlacement d hF e hA)⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
