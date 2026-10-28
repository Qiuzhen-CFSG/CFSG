module

public import Stellmacher.SectionOne.Defs
public import Stellmacher.SectionOne.GLFourTwoClassification
public import Stellmacher.SectionOne.InvolutionPGroupSmallIndexClassification
public import Stellmacher.SectionOne.CenterThreeGF4Embedding
public import Stellmacher.SectionOne.OrderTwoSylowInvolutions
public import Stellmacher.SectionOne.SLThreeFourClassification
public import Stellmacher.SectionOne.RankOneLocalSL2Coordinate
public import Stellmacher.SectionOne.RankOneLocalFullCoordinate
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Generic
public import Stellmacher.SectionOne.LemmaOneSixSmallM
public import Stellmacher.SectionOne.LemmaOneOne
public import Stellmacher.SectionOne.LemmaOneTwo
public import Stellmacher.SectionOne.LemmaOneThree
public import Stellmacher.SectionOne.LemmaOneSeven
public import Stellmacher.SectionOne.OneSevenDihedralQuotient
public import Stellmacher.SectionOne.OneSevenSmallSylow
public import Stellmacher.SectionOne.OneSevenSylowLines

/-!
# Stellmacher, Section 1

Public wrapper for the shared Section 1 definitions, the `GL₄(2)` endpoint,
the reduced small-index involution `p`-group classification, the center-three
`GF(4)` representation, and the `SL₃(4)` finite-linear
classification endpoint used by Lemma (1.3), the
order-two Sylow involution structure used by Lemma (1.6), and the three
introductory numbered results.  It also exports the local `SL₂(2)` coordinate
package, its full fixed-index upgrade, and the proved generic alternatives
(c)/(d) in the rank-at-least-two assembly of Lemma (1.6), and the complete
recursive classification in the offender range `m(S) ≤ 1`, together with
the complete global offender and module decomposition in (1.7). Other numbered
results live in one file each under `Stellmacher.SectionOne`; the small-Sylow
and odd-dihedral quotient corollaries extract from (1.7) the `SL₂(2)` endpoint
used later in Section 8.  The Sylow-line module records the intrinsic
order-two support control used by the commutator-line argument in (4.6).
-/
