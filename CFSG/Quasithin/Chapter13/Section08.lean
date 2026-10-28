module

public import CFSG.Quasithin.Chapter13.Section08.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceCriticalGeometry
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceLocalImage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalCorePlacement.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalSource
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceReduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.NormalSource
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Source
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint.Ordinary
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.Cover
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalConjugates
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalExchange
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalIntersections
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalMovement
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalKernel
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalCentralizer
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalChiefBounds
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalCubicBounds
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergObstruction
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergComparison
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergSmallMovement
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalQuadratic
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.AmbientComparison
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalPlanes

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixComplete
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups.OriginalSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.NativeSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.C3System
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.Complete
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Complete
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCover
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverOrbit
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverPoint
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverPlane
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverRecognition
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalWholePermutation
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalWholeComparison
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalWholeCover
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalSmallMovement
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalEndpointCore
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalSeedCentralizer
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCentralizerAction
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCentralizerPermutation
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCentralizerCubic
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalLeftFiltration
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalRightFiltration
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalRanks
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalTerminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Terminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Original

/-!
# Finishing the treatment of A₆: source reductions and conditional assembly

Theorem 13.8.1 of Aschbacher–Smith asserts that, under Hypothesis 13.3.1,
`L/O₂,Z(L) ≅ A₆` implies `G ≅ Sp₆(2)` or `G ≅ U₄(3)`. Its proof occupies
§13.8, printed pp.946–969 (PDF pp.963–986), of the combined manuscript
of 1 March 2004. The last contradiction continues onto p.969.

This module proves the elementary arguments in 13.8.3 and 13.8.9(1)
from their explicit local inputs. For 13.8.3, move a nonidentity element
of an intersection to the distinguished element and apply centralizer
fusion. For 13.8.9(1), normal generation would make the entire quotient
central if the proposed commutator vanished.

`Components.Source` combines the original exchanged linear-two and
linear-three exclusions with the full natural central-section recognitions
for both Suzuki orbit cases. It proves relative component normality and the
concrete catalogue on the literal star image, and applies the completed
original 13.3.9 residual input. Its field-component geometry application
supplies normality and quasisimplicity from these source theorems. The
original setup, F.9 and 13.5.4 hypotheses remain earlier-source inputs.

`LinearReduction.OriginalSource.Complete` applies the completed field and
cover sieve to original 13.8.24–25. It supplies the uniform A₇ exclusion,
the degree-four and covered-quotient conclusions, H = G₁, and compatible
natural coordinates on the whole U_H/V₁ under literal conjugation.
The genuine earlier-source hypotheses retain their original contracts.

`ComponentSieve.SixAndG2.SourceAssembly` assembles the marked 13.8.27
dichotomy, G₁ = H = KT and case-one symmetry from the explicit preceding
source inputs. Its terminal application constructs the ordinary syntheme-edge
and module-plane markings, and the covered L₄ setup with the actual endpoint
module of order 32.

`SourceCompletion.OrdinaryAssembly` connects the actual maximal ordinary
A₆ source choice to both terminal denominator cases. It supplies the
abelian closure, F.9 geometry, Hz choice and ambient centralizer inputs
from their earlier source applications. The full-denominator case uses
the actual compatible chief-filtration maps; the strict case derives
the ranks and line containments before applying the point-normalizer model.

`SourceCompletion.TerminalPoint.Ordinary` constructs that point-normalizer
model from the recognized component section. It proves movement by O₂(H)
and nonfixedness in the literal quotient, and constructs the full natural
or augmentation coordinates while retaining the cover's constant line.

`SourceCompletion.CaseOne` proves abelianness of the L-span in the cover
branch. In the contrary nonabelian natural branch it constructs the moved
seed complement and conjugator, proves quotient irreducibility, identifies
the literal star image with O₂(L₁*), and establishes the centralizer index
and commutator bounds. It then centralizes H_C/V_H by O²(H) and bounds
the noncentral H-chief factors on the literal V_H/U_H by one. The
surviving constituent is a natural four-space, giving cubic length at
most two on this quotient. The original central duality then bounds cubic
length on Q_H by six and on the common local two-core by seven. The
published sixteen-dimensional tensor contributes six. The original two
local planes and their parabolic markings construct its quotient,
the natural V section, the parabolic-core quotient and a surjective cubic
lift. These give length at least eight and prove abelianness of U_L.
The same recognized quotient also excludes an involution moving at most
two dimensions on U_L/V. Full denominators now construct the original S₆
bar; simultaneous flag coordinates and the H-side seed stabilizer derive
all three parabolic markings. The comparison with the original local planes
therefore assumes none of these markings. Abelianness also yields mutual
normalization and quadratic action of U_L and Uγ on the actual groups.
Instantiation of the local planes, the ambient small-movement estimate,
and the later permutation and 13.4.1 arguments remain required to establish
strict denominators.

The preceding classification, escape and plane inputs, component supplement,
and marked 13.8.33 models remain explicit. The 13.8.27 assembly retains its
earlier-source hypotheses. The covered local quotient also retains its separate
13.8.28–32 obligation. These conditional theorems do not assert Theorem 13.8.1
or discharge those missing source inputs.

The statement of 13.8.10 on printed p.950 has `U_H < D_H`; its definition
and proof instead use `D_H < U_H`. A source application must use the
latter inequality, rather than derive a vacuous result from the former.
-/
