module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Quotient
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientModel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.CoordinateConstruction

/-!
# The counted max2 quotient is no larger than the actual outer-action image

For the actual local subgroup H and seed normal closure N, the quotient
N/<t> has the twelve specified binary coordinates. The certified conjugation
tables and invertible simultaneous change of basis realize the literal
`LowerBound.quotientSubgroup` in its action image. Inner automorphisms of N
act trivially on N/<t>, so that image is a quotient of the actual image of
H/N -> Out(N). Combining these maps gives the stated cardinality comparison.

Every coordinate and kernel premise is discharged here. The numerical order
of the independently counted matrix subgroup is not needed. Neither whole
involution-centralizer generation nor an ATLAS group identification is used.
Source motivation: GLS3 Table 5.3i, printed p.270. Word and matrix provenance
is documented in `ActionKernel/Presentation/source/README.md`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- Compare the literal matrix subgroup with the actual conjugation-induced outer image. -/
theorem quotientSubgroup_card_le_localNormalClosureOuterAction_range :
    Nat.card LowerBound.quotientSubgroup ≤ Nat.card localNormalClosureOuterAction.range :=
  OuterImageComparison.card_comparison_of_coordinates
    OuterImageComparison.coordinates OuterImageComparison.coordinates_respectsBasis

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
