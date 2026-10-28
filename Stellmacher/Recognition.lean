module

public import Stellmacher.Recognition.NGroup
public import Stellmacher.Recognition.NGroupTransport
public import Stellmacher.Recognition.SimpleReduction
public import Stellmacher.Recognition.Sp4TwoExclusion
public import Stellmacher.Recognition.CatalogueReduction
public import Stellmacher.Recognition.CharacteristicThree
public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Stellmacher.Recognition.GTwoSylow
public import Stellmacher.Recognition.MaximalC2S4Centralizer
public import Stellmacher.Recognition.NGroupReduction
public import Stellmacher.Recognition.OddCoreBalance
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Stellmacher.Recognition.Sylow32C2S4
public import Stellmacher.Recognition.NTwoGroupQuotient
public import Stellmacher.Recognition.OddCoreClosure
public import Stellmacher.Recognition.Parrott.DerivedNormalizer
public import Stellmacher.SectionEleven.MultipleMaximalRichTerminal
public import Stellmacher.Recognition.TerminalReduction
public import Stellmacher.Recognition.TerminalResidualReduction
public import Stellmacher.Recognition.ClassificationOfOddCore
public import Stellmacher.Recognition.FinalTheorem
public import Stellmacher.Recognition.LargeTerminalResidual
public import Stellmacher.Recognition.Parrott.FusionOutsideDerived
public import Stellmacher.Recognition.SourceCharacteristicThree
public import Stellmacher.Recognition.LargeTerminalCentralizerCore
public import Stellmacher.Recognition.LargeTerminalSmallCore
public import Stellmacher.Recognition.LargeTerminalFiveAction
public import Stellmacher.Recognition.CoreFreeSemidihedralCentralizer
public import Stellmacher.Recognition.SemidihedralSylowSixteen
public import Stellmacher.Recognition.SylowSpectrum
public import Stellmacher.Recognition.Sylow32C2D8Embedding
public import Stellmacher.Recognition.LargeTerminalSmallFive
public import Stellmacher.Recognition.GTwoAbelianBase
public import Stellmacher.Recognition.GTwoSixtyFourLocal
public import Stellmacher.Recognition.Sylow32Exclusion
public import Stellmacher.Recognition.LargeTerminalResidualNormal
public import Stellmacher.Recognition.OddCoreCompletion
public import Stellmacher.Recognition.OddCoreStrongEmbedding
public import Stellmacher.Recognition.OddCoreComponentNormalizer
public import Stellmacher.Recognition.OddCoreSmallRank
public import Stellmacher.Recognition.OddCoreBinaryFusion
public import Stellmacher.Recognition.OddCoreRankThree
public import Stellmacher.Recognition.GTwoWreathed
public import Stellmacher.Recognition.TitsLocalSylowLower
public import Stellmacher.Recognition.LargeTerminalParrott
public import Stellmacher.Recognition.LargeTerminalReeExclusion
public import Stellmacher.Recognition.LargeTerminalSylowOrder
public import Theory.GroupTheory.ElementaryInvolutionFixedJoin

/-!
# The global simple N₂ and N classifications

`Stellmacher.nTwo_classification` and `Stellmacher.n_classification` give
actual catalogue model isomorphisms for finite nonsolvable simple groups.
The Tits group is included, and only the N₂ catalogue has the extra even-field
unitary family. The final assembly discharges the Lyons character calculation
and the odd-core recognition input as well as every terminal local branch.

The original all-prime local-solvability predicate specializes to the N2
predicate used by the completed local classification. For nonsolvable simple
groups the recognition reduction supplies actual Bender--Suzuki and
Gorenstein--Walter models, including recognition of the local L3(2) branch.
The local Sp₄(2) type is excluded by square lifting and Thompson transfer.
The catalogue reduction collects the recognized branches as actual model
isomorphisms with the source parameter bounds. Solvable involution
centralizers force the ABG source characteristic parameter to be three.
With trivial two-local odd cores, the simple semidihedral branch has actual
GL2(3) involution centralizers and its supplied Sylow has order sixteen. Parrott's
original centralizer hypotheses give the core structure and an actual
ambient Sylow subgroup. The G2 local type forces ambient Sylow order 32
or 64; a maximal C2 times S4 subgroup is a full involution centralizer.
The all-prime N condition excludes every extra even-unitary model, and
commuting involution centralizers satisfy the odd-core balance condition.
Glauberman's Z-star theorem supplies a distinct Sylow conjugate for each
simple-group involution. Parrott's derived elementary subgroup has the
prescribed normalizer in an N2 group, and a conjugate of its central
involution escapes the derived subgroup. The refined simple-group reduction
retains the actual large Section Ten context and trivial two-local odd cores.
The first residual has order 512 and class three, with its center and derived
subgroup identified in the original ambient group. It lies in the two-core
of a full ambient involution centralizer, inside the second member's two-core.
For Sylow order2048 that full core equals the residual. An actual order-five
subgroup acts on the residual with fixed subgroup contained in its center.
The N2 condition descends to quotients, and the odd-core closure is unchanged
on elementary subgroups of rank at least two. Ordinary transfer excludes the
order-32 maximal C2 times S4 configuration. The actual odd-core closure on
an elementary subgroup of rank at least three is odd and solvable, with exact
recovery of its local cores by centralizer intersections. Its closure is constant
on elementary commuting components; a nontrivial closure has a proper
normalizer controlling that component. Binary normalizer control and
Bender–Suzuki elimination force every rank-three closure to be trivial.
The order32 G2 branch has an actual
wreathed Sylow subgroup of height two. The completed semidihedral recognition
and order-64 G₂ exclusion refine the unconditional terminal reduction to the
G₂ type with supplied Sylow order 32, the actual large terminal context with
Sylow order 2048 or 4096, and the genuine bad-odd-core alternative. Both
local branches retain trivial two-local odd cores. The completed
local theorems are re-exported through the reduction.
The twisted-F4 local data also transfer their raw `2^11` lower bound to the
actual ambient Sylow.
In the order-64 G2 branch, both vertices have order 192 and two-core order
32, the second core is a quaternion central product, and the first core has
an outside inverter of its normal C4 times C4 base. This base has index four
in each ambient Sylow subgroup.
For Sylow order 2048, the retained large terminal context supplies all of
Parrott's original full-centralizer hypotheses, including the actual
Frobenius-20 quotient model.
The elementary fixed-join normalizer geometry needed by Parrott's remaining
core-involution argument is also exported from the theory layer.

Source: Thompson's N-group theorem and its N₂ generalizations, with exact
catalogue and recognition sources in `Recognition.FinalTheorem` and the
imported modules.
-/
