module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.QuotientClassification
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.SharpImage
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.OctadSaturation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows.Classification
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.LinearFiveRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.CoverAssembly.Elementary
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.NativeLinearFive
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.UnitaryExclusion

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.Reductions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.ResidualQuotients
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MaximalOvergroup
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.MaximalLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.CenterBounds
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstPair
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.ElementaryForm
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSymmetryReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstResidualCharacter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstRepresentativeForward
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondPairs
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSwaps
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondKernelPairs
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.MixedPairs
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.Symmetry

/-! Large-center radical reductions for the native J₄ carrier. The imported
modules prove the full-core identity, the maximal-overgroup reduction, small-
center local exclusions and the radical-core construction for maximal
two-locals. Normal residuals with the original U₃(3) or SL₃(2) quotient
marking exclude the three candidate simple quotients. Full intrinsic
commuting-involution symmetry and the resulting normalizer-invariant
alternating form on every elementary subgroup are proved. The native kernel
and octad-preimage radical rows have their actual M24 and A8 quotients, with
full intrinsic cores and all conjugation transports. In the Mathieu branch,
a large-center radical has elementary image of order at most sixteen.
Any nontrivial radical image contained in an octad kernel equals that kernel.
The native F row and its conjugates have their proved SL₅(2) quotient.
For every radical placed in N(F), its literal linear image retains the full
normalizer quotient and its exterior fixed space has exactly the original
center size. Every such large-center radical now has full normalizer quotient
SL₅(2) or A₈, including arbitrary conjugate placements. Conditional cover
assembly proves both residual contradictions. The complete native cover is supplied by the CFSG-layer
`PureFirstNormalizers.CompleteCover` assembly. The Mathieu image classification is complete: cyclic radicals are excluded
by their whole centralizers, and the certified fixed-space bound places every
noncyclic image in an octad kernel. Radical saturation gives the full A₈
quotient; the trivial image gives M₂₄. `QuotientClassification` combines both
native local branches. The CFSG-layer `JankoLargeCenterRadical.NativeQuotients`
supplies the actual completed cover and exports the unconditional arbitrary-
radical quotient theorem, full core identity and both normal-residual exclusions. -/
