module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.SourceCharts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalSection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalAllFields
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalCrossingApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.ReflectedApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.LinearApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.DerivedApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.DerivedRootApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.Assembly
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.FieldApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.CenterApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NaturalFlagApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.MixedApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.PositiveApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.CartanApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.BruhatApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.WeylApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.NativeData
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.SourceComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.GeometricComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.Chapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.GeometricChapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.PerfectFactorApplication

/-!
# U₅ source recognition and marked comparisons

This umbrella exports the source charts, natural-section coordinates in every
positive binary field degree, the Hermitian realization of the actual linear
radical-derived subgroup, and the constructed `FiveData` with its marked
projective and published-model comparisons.
The coordinates preserve the original SU₃ covering and projective panel maps,
including q = 2. The derived realization preserves the original SL₂ marking
and its literal quotient representatives. Its two diagonal lines now identify
the entire unitary-root centers, and its off-diagonal plane identifies the
crossed linear root. The trace and central-root crossing equations and the
specified linear reflection action hold in these coordinates, with literal
original Q.q product formulas. The SU₃ natural coordinates now pin its whole
root and give a faithful crossed-linear chart and a surjective coordinate
on the whole crossed unitary root, with its intrinsic center as kernel.
Their B–D crossing holds exactly on original Q.q representatives.
The reflected pairing now gives compatible full nonabelian B and D charts
and a normalized C chart on the same Hermitian field. The exact B–D law and
the specified linear reflection use these common labels, including q = 2
and q = 4. The actual linear Frattini section now has natural SL₂
coordinates; both whole unitary roots fill its coordinate axes, with their
full centers as kernels. Comparison with the SU₃ charts constructs one
additive field label used on both B and D. Comparing the same A–B commutator
in the two natural sections proves that this label is a nonzero scalar
times a field isomorphism and synchronizes the A parameter. The derived
Hermitian C chart and both full root centers then use this common field
with one shared nonzero fixed-field scalar. Frobenius compatibility gives
the actual trace and central B–A norm laws on original Q.q products.
The specified unitary reflection now pins the whole natural flag by an
explicit inner root change, preserving both actor markings and root labels.
The actual linear Cartan word determines the remaining central norm
coefficient. The synchronized whole roots satisfy all six positive-root
relations and all four linear coroot actions, with literal original Q.q
formulas and unique coverage of the original Sylow image. The full
two-parameter Cartan now lies in the literal source B ∩ N and satisfies
all four presentation actions, including both nonabelian roots and their
centers. Both exact rank-one Bruhat formulas now use this same Cartan,
with the specified linear reflection and the actual SU₃ Weyl image. The
linear reflection swaps the entire B,D roots and conjugates the C label.
The unitary Weyl image lies in the actual marked normalizer, exchanges A,C
and fixes the whole D root, including its center. Both Cartan reflection
identities and the braid hold for these same lifts. Original source
generation then constructs `FiveData`, using Cartan range inclusion alone.
The resulting projective comparison identifies the full scalar kernel,
both endpoints and the whole Borel, retaining literal original Q.q and the
marked geometric comparison interface. The concrete geometric specialization
constructs its marking and recovers the quotientMap squares in either orientation.
Its Chapter12 consumer restores the original amalgam directly from the actual
reduced amalgam's apartment quotient, retaining the explicit apartment geometry,
root quotient data, split datum, rotation order and mixed-factor profile.
Finite-field transport
gives the published model in every source universe. The proved
`FiveSourceTheorem` feeds the original Chapter12 restoration and residual
exit, with the earlier quotient, split datum and row-selection hypotheses
retained. The actual selected perfect-factor application constructs its
profile from the original mixed-factor marking, preserves the field-degree
relation and both core preimages, and supplies the concrete amalgam comparison.

Source: Fong--Seitz I (6A)(c), II (8C), pp.202–210; DGS Theorem D and
(15.2), pp.224–228; Aschbacher–Smith F.1.12 and 12.2.1.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
