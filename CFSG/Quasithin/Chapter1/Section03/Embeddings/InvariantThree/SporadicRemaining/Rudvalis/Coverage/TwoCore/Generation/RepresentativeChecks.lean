module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Initial
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0062
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0126
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0190
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0254
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0318
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0382
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0446
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0510
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0574
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0638
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0702
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0766
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Batch0830

/-!
# Complete normalization-or-recovery checks for the Rudvalis representatives

All 847 published representatives satisfy the exact three-way alternative.
The first six lie in max4 and normalize its intrinsic two-core. Indices 839
and 840 centralize the intrinsic center of the fixed Sylow subgroup. For
every other index, kernel-checked word certificates recover both original
standard generators in the specified inverse-closed extension alphabet.

This module proves the representative checks only. Exhaustiveness of the
prospective double-coset family belongs to the separate coverage argument.
No coverage or maximality premise, normalizer identification, or max4/max6
cardinality bound is assumed here.

Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher (1986), no.343. The actual ATLAS carrier, intrinsic core and center,
and word-action comparisons are those in `Representatives`, `Base`, and `Center`.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
open Representatives

/-- Every index has intrinsic normalization or both standard-generator words. -/
public theorem all_representatives (i : Index) : Alternative i := by
  by_cases h0 : i.val < 6
  · exact first_six i h0
  by_cases h1 : i.val < 62
  · exact initial_recovery i (by omega) h1
  by_cases h126 : i.val < 126
  · exact Batch0062.checked i (by omega) h126
  by_cases h190 : i.val < 190
  · exact Batch0126.checked i (by omega) h190
  by_cases h254 : i.val < 254
  · exact Batch0190.checked i (by omega) h254
  by_cases h318 : i.val < 318
  · exact Batch0254.checked i (by omega) h318
  by_cases h382 : i.val < 382
  · exact Batch0318.checked i (by omega) h382
  by_cases h446 : i.val < 446
  · exact Batch0382.checked i (by omega) h446
  by_cases h510 : i.val < 510
  · exact Batch0446.checked i (by omega) h510
  by_cases h574 : i.val < 574
  · exact Batch0510.checked i (by omega) h574
  by_cases h638 : i.val < 638
  · exact Batch0574.checked i (by omega) h638
  by_cases h702 : i.val < 702
  · exact Batch0638.checked i (by omega) h702
  by_cases h766 : i.val < 766
  · exact Batch0702.checked i (by omega) h766
  by_cases h830 : i.val < 830
  · exact Batch0766.checked i (by omega) h830
  exact Batch0830.checked i (by omega) i.isLt

end Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
