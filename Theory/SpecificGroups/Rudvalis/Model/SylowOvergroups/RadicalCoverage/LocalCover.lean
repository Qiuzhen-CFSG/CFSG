module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Proper
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers

/-!
# The fixed-Sylow Rudvalis radical-normalizer calculation

The fixed word subgroup is Sylow in max4, and every nontrivial normal
elementary subgroup of it belongs to the six-candidate catalogue. The
candidates' ambient normalizers lie in max4 or in a certified conjugate
of max6. For a radical subgroup U
normal inside this Sylow subgroup, Ω₁(Z(U)) belongs to the catalogue and
its normalizer contains N(U). Properness of the two candidates turns
maximality of N(U) into an actual multiplicative equivalence.

`max4RadicalNormalizerCover` assembles the proved intrinsic Sylow,
catalogue, and both ambient normalizer bounds without extra premises.
The outer `RadicalCoverage` owner handles ambient Sylow status and global
conjugacy.

Source: the [Asc86b] Sylow-overgroup analysis used in Aschbacher--Smith,
printed p.511 (PDF p.528), and the attributed ATLAS subgroup programs
preserved in `SylowOvergroups.Definitions`.
-/

namespace Rudvalis.SylowOvergroups

open RadicalCoverage.LocalCover

/-- For one Sylow two-subgroup of the original ATLAS max4, every maximal
ambient normalizer of a radical subgroup normal inside it is isomorphic
to the original max4 or max6. All fixed-word certificates are discharged. -/
public theorem max4RadicalNormalizerCover : Max4RadicalNormalizerCover :=
  radicalCover_of_elementary intrinsicSylow elementaryCatalogue
    (elementaryNormalizerCover_of_bounds max4NormalizerBounds max6NormalizerBounds)

end Rudvalis.SylowOvergroups
