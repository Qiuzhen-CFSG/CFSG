module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearFlags
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.BinaryMarked

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.SourceActions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeMarking
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.MSPreparation
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Remaining
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingSymplectic

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingSmall
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingAlternating
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingPermutation
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.SourceRemaining

/-!
# Preparation for the marked component reduction in original 15.2.23

The source selects an escaping component and gives the C.2.4 full-Sylow or
normalization dichotomy. The conditional normalization connector isolates
the exact outstanding C.2.4(1) chi-zero implication. For a normalized
selection, the unrestricted moved section, actual star models, central
core-to-star kernel and proper Thompson marking are proved consequences.

Both L₄(2) and L₅(2) now construct the original marked positive-rank
parabolic from their actual star-model isomorphisms. The original Sylow
intersection supplies the flag overgroup. The two-group marking would
force a forbidden chi-zero block, so the flag has positive rank. The
earlier unrestricted L₅(2) Thompson-placement route remains available.

The full B.5.1 source-action reduction removes natural rank one and all
binary rows using the original block and small-action contradictions. It
retains the full moved-section conclusion and each surviving action's
markings and offender clauses, on the same selected component.

The natural and doubled SL₃ rows now derive the actual Thompson placement
and marked maximal parabolic, including the binary field. The original NI
also supplies the odd-index MS witness, and characteristic control supplies
MS3 on XR. Full core-quotient recognition now supplies the complete SL₃
model. The source geometry forces degree one before applying the existing
small MS classifier, which gives the original MS description with all five
module alternatives. The corrected small-action contradiction excludes both
linear-three rows on that marking. The completed terminal binary source
also removes the KS quotient premise from the remaining-action consumer.
Its original B.5.1 conclusion and all surviving nonlinear action clauses
are retained; the small MS classifier remains an explicit earlier source.

The exhaustive reduction to `ComponentCatalogue.LinearAlternative` remains
open. It needs the marked non-chi C.2.7 catalogue and its elimination using
the original K, S and plane centralizer; group-family identifications alone
do not supply it. Final assembly of that reduction belongs to this module.


All symplectic rows and the A₆ row are now excluded. The nonbinary
symplectic proof uses the original full-core parabolic. The A₆ argument
retains its possible cubic kernel and discharges it through the existing
small MS classification. The same original full quotient and radical
normalizer also exclude every nonbinary G₂ field, without an MS input.
The binary G₂ row is also excluded: its full core quotient and outer
two-group place the original K in X, whereas the proper partner
intersection has three-rank at most one. The triple-six action is excluded
by placing its cubic central preimage in the original NI and applying
the rank-two intersection obstruction to K. RemainingPermutation keeps
the full moved section and all surviving clauses on the same selected X.
The symmetric-five/seven and exceptional A₇ rows, full original KS
placement, and source assembly remain open.

The unconditional source reduction is now `SourceRemaining`. It uses the
model-only linear-three exclusions and retains the same original component
and full moved section. Its alternatives are the surviving permutation
actions or an A₆ star image whose full core quotient has cubic center.
The older reductions using `EarlierMSClassifications` remain conditional:
its universal linear-three module field is refuted by `MS/F4Obstruction`.
Only the actual A₆ pair's rank-two conclusion is needed for that row's
existing exclusion; it remains an earlier-source obligation.

Source: Aschbacher--Smith, 15.2.23, printed pp.1116--1117, and C.2.4--7,
printed pp.144--147; refs/quasithin.pdf.
-/
