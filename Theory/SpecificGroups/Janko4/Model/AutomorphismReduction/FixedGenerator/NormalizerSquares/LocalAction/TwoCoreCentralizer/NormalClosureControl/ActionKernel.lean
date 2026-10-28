module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.CentralizerReduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder

/-!
# Control of the max2 conjugation kernel

For the concrete max2 subgroup H and its seed normal closure N, the 29
certified relator lifts and finite presentation cover give |H/N| ≤ 2661120.
The independently counted matrix subgroup has at least 2661120 elements,
and the proved coordinate comparison bounds its order by the image of
the actual outer action H/N → Out(N). These matching bounds force that
action to be injective. Therefore every element of H centralizing N
belongs to N.

All finite bounds and coordinate premises are discharged by the imported
certificates. The statement concerns the centralizer relative to H.
Source motivation: GLS3 Table 5.3i, printed p.270; concrete provenance is in
`ActionKernel/Presentation/source/README.md` and `Max2Bridge`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The matrix relators have been discharged; only the two finite bounds remain. -/
theorem localNormalClosureAction_ker_le_of_presentation_and_image_bounds
    (hpresentation : Finite NormalClosureControl.ActionKernel.Presentation.Group ∧
      Nat.card NormalClosureControl.ActionKernel.Presentation.Group ≤ 2661120)
    (himage : 2661120 ≤ Nat.card localNormalClosureOuterAction.range) :
    localNormalClosureAction.ker ≤ localNormalClosure :=
  localNormalClosureAction_ker_le_of_card_bounds
    (NormalClosureControl.ActionKernel.Presentation.quotient_card_le_of_presentation_bound
      hpresentation) himage

/-- Every element of the concrete max2 subgroup centralizing its seed normal
closure belongs to that normal closure. -/
theorem localNormalClosureAction_ker_le :
    localNormalClosureAction.ker ≤ localNormalClosure :=
  localNormalClosureAction_ker_le_of_presentation_and_image_bounds
    NormalClosureControl.ActionKernel.Presentation.presentation_finite_card_le
    (LowerBound.quotientSubgroup_card_ge.trans
      quotientSubgroup_card_le_localNormalClosureOuterAction_range)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
