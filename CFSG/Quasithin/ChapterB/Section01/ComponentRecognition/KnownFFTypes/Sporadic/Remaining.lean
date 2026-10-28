module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Remaining.Criteria

/-!
# Assembly of quantitative sporadic normalizer exclusions

The FF condition supplies a nonidentity involution of displacement at most the
automorphism two-rank of the actual simple quotient. A strict displacement
bound contradicts it. Alternatively, a degree lower bound and generation by
conjugates give the strict displacement bound by intersecting fixed spaces.

The shared criteria are re-exported from `Remaining.Criteria`, so model
producers can import them without depending on this final assembly module.
All model bounds remain explicit here. This module does not yet assert the
eight exclusions for He, Fi₂₂, Fi₂₃, Fi₂₄′, HN, Th, B and M. Their quantitative
producers must account for arbitrary central covers, outer normalizer elements,
and the exact carriers in `CFSG.KnownSimple.SporadicCarriers`.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 / PDF pp.84–85, and its
reference to Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117.
-/

