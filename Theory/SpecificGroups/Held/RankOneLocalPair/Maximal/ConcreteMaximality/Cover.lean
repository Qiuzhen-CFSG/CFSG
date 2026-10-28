module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Alignment

/-!
# Unconditional cover certificate for Held max5

The literal 4,831 left factors commute with max5First^4. Every row is checked
on the proved four-point base of the existing Held carrier, using certified
packed generator and conjugator tables. The checked words are proved equal
to the original data; no external computation is trusted.

This discharges the cover premise of `ConcreteMaximality.covers_of_checks`
and `max5_isCoatom_of_checks`. Generator recovery is an independent premise.
Source: ATLAS HeG1-max5W1; the maximal local used in Aschbacher–Smith
E.1.14(4), printed p.214. See ConcreteMaximality/source/README.md.
-/

namespace Held.RankOneLocalPair.ConcreteMaximality

/-- Every literal left factor of the max5 double-coset reduction centralizes its involution. -/
public theorem coverChecks : CoverChecks := by
  intro j
  apply CoverCertificate.rowCheck_sound j
  rw [CoverCertificate.actualRow_eq_certificateRow]
  exact CoverCertificate.certificate_checked j

end Held.RankOneLocalPair.ConcreteMaximality
