module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Proper
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover

/-!
# Rudvalis maximal radical normalizers

Every maximal normalizer of a nontrivial two-radical subgroup with odd
normalizer index is isomorphic to the preserved ATLAS max4 or max6.

The ambient Sylow certificate in `RadicalCoverage.Sylow` makes the Sylow
subgroup used by `RadicalCoverage.LocalCover` ambient Sylow as well.
The reduction in `RadicalCoverage.Reduction` conjugates the radical subgroup
into this Sylow subgroup, retaining normality there. The local cover and
properness of the candidates then supply actual multiplicative equivalences,
which conjugation transports back to the original normalizer.
All concrete premises are discharged by the two imported certificates.

Source: Aschbacher--Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), citing [Asc86b]. The actual ATLAS subgroups are preserved in
`SylowOvergroups.Definitions`.
-/

namespace Rudvalis.SylowOvergroups

/-- Every odd-index maximal normalizer of a nontrivial two-radical subgroup
of the original Rudvalis model is isomorphic to the ATLAS max4 or max6. -/
public theorem oddIndexMaximalRadicalCover : OddIndexMaximalRadicalCover :=
  oddIndexMaximalRadicalCover_of_max4 max4ContainsSylow max4RadicalNormalizerCover

end Rudvalis.SylowOvergroups
