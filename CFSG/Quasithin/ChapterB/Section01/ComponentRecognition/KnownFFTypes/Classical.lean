module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.RankOne

/-!
# The classical contribution to general FF recognition in B.1.13

`Classical.Conclusion` describes actual characteristic-two Lie carriers
for the original covering group, or an actual alternating simple central
quotient. It retains all six classical families and the derived G₂(2)
carrier required for the exceptional PSU₃(3) alias.

The complete rank-one results establish this conclusion for every even
PSL₂(q) parameter and for q = 5, 7, 9. They use proved universal covers
and concrete exceptional isomorphisms; they need no FF or SQTK assumption.

The general source branch is not yet proved. Its remaining obligations
are the even-field covering identifications in the other families and
the odd-field FF exclusions, including all small aliases. These must use
the full linear normalizer action from `NormalizerExtension`, and must
discharge any extra hypotheses of the representation classification.
In particular, no assertion that this normalizer has quasisimple
generalized Fitting subgroup is assumed here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, B.1.13, printed pp.73–74, citing
Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117. The completed rank-one results use the
separate covering sources documented in `Classical.RankOne`.
-/
