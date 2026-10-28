module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.Preparation
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.LocalReduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Consequences
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Parabolic
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.TwoCoreAction

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.ResidualCentralizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Normalizer

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.InvolutionAssembly
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.CentralizerControl
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Fusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SwappingGeometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SwappingNormalizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SwappingKernel
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.CentralSylowKernel
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.FixedKernel
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.EnlargedSwapping
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SixCoordinates
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SixWords

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Construction

/-!
# The selected-counterexample order-32 branch

The original closure is a quaternion central product of order 32, and the
literal source geometry supplies V = O₂(L), U = O₂(L₁), T∩L = UWᵍ,
and M = LT. The c₂ branch uses the elementary ambient core and Thompson
transfer to construct the required local data.

In the swapping branch, the actual split block and Sylow placement identify
A = Jₑ(T∩L), with N_H(A) = T. The remaining central kernel has order four,
and B = A C_G(L) is elementary of order 64. Its marked parabolic fixes the
central plane, while a cubic from H normalizes B and moves both factors.
The literal six-dimensional coordinates give a faithful image whose marked
point stabilizer has element orders dividing 4608. An exhaustive basis-image
parameterization, followed by the checked representative words, produces a
point-fixing element of order seven and excludes this last swapping case.

`source_localData` now constructs both core equalities, quotient order 18,
and the actual inverter and generation identities. `source_configuration`
applies them to construct the genuine I.4.5 configuration on H and L.
The independent universal I.4.5 recognition theorem remains required for
the final equivalence with the actual G₂(3) model. Earlier-source inputs
retain their existing producers and final discharge in qt-d-14414-source.

Source: Aschbacher–Smith, 14.4.2–5, printed pp.1006–1008.
-/
