module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Square
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Radical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.CenterAssembly

/-!
# Support for the binary distance-four branch of MS93

The actual natural U_alpha lies in the center of [Q_alpha,Ltilde_alpha].
The module calculations supply the square-map vanishing and the nondegeneracy
of a nonzero pairing between two dual factors. `Source` specifies the remaining
local and quotient constructions, with the actual amalgam groups and action.
The early source facts through (4.6.7), including derived noncentrality and
the radius-center equality, follow from CommonFacts and b = 4 via
`DistanceFour.earlyFacts`.

This module does not yet prove MS93 (4.6) from LocalSource, Geometry,
CommonFacts and b = 4. `CenterAssembly` constructs the actual square and
commutator maps from DoubleDualQuotient and proves the core-center equality.
It also applies the existing conditional quotient constructor. The radius
facts follow from `earlyFacts` and `Flags.radiusFacts`; the large-orbit branch
of the quotient constructor remains to be supplied. No record field asserts
the desired center equality.
-/
