module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.LineOrbit
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.RowOrbit0
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.RowOrbit1

/-!
# The line stabilizer excludes order 6912

The existing concrete orbit certificates determine the order of the actual
stabilizer of the line {23, 1024, 1047}. Its 231 distinct translates give an
upper bound of 11520. Two certified words inside the stabilizer generate a
subgroup with a 960-point row orbit and a row stabilizer of order at least 12,
giving the matching lower bound. Thus 6912 cannot divide its order.

`LineOverlapCertificate.line_stabilizer_bound` bridges the action conventions:
forward right multiplication is `rowAction` applied to the inverse, and a
subgroup is closed under inversion. The lower-bound words are certified in
the inverse-action stabilizer itself. No candidate recognition or untrusted
witness conclusion is assumed here.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528
of `refs/quasithin.pdf`; GLS3 Table 5.3i. The finite certificates and their
provenance are in `QuotientIncidence/LineOverlap/source/`.
-/

public section
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2

/-- The order of the actual matrix line stabilizer is not divisible by 6912. -/
theorem line_order_not_divisible_6912 : ¬ 6912 ∣ Nat.card involutionMatrixLineStabilizer := by
  have hupper := LineOverlapCertificate.line_stabilizer_bound
  rw [involutionMatrixQuotient_card] at hupper
  have h0 := LineOverlapCertificate.level0_bound
  have h1 := LineOverlapCertificate.level1_bound
  have hmap : Nat.card LineOverlapCertificate.generatedUnits =
      Nat.card involutionMatrixLineGenerated :=
    Subgroup.card_map_of_injective LowerBound.quotientSubgroup.subtype_injective
  rw [hmap] at h0
  have hsub := Subgroup.card_le_of_le LineOverlapCertificate.generated_le_stabilizer
  have hcard : Nat.card involutionMatrixLineStabilizer = 11520 := by omega
  rw [hcard]
  decide +kernel

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2
