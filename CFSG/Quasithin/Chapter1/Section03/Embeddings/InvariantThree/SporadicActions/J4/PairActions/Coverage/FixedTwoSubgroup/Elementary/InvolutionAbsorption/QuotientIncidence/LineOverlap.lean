module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.SourceLifts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.RowOrbit0
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.RowOrbit1
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.LineOrbit

/-!
# The full inverse image of the specified max2 quotient line stabilizer

Two explicit words generate the line stabilizer. Their checked row orbits
supply a lower bound of 960 · 12 = 11520. The checked 231 line translates,
together with the proved quotient order 2661120, give the matching upper
bound. The full inverse image is consequently the join of the two source
word lifts and the actual two-core.

The checked ambient word certificates put all thirteen core generators and
both word lifts in one conjugate of the actual ATLAS max4 subgroup. The exact
finite membership criterion then places the entire inverse image, including
the two-core, in that same conjugate.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher, *Overgroups of Sylow
subgroups in sporadic groups* (1986); GLS3 Table 5.3i, printed p.270.
The matrix and orbit certificate provenance is in `LineOverlap/source/`.
-/

@[expose] public section
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

attribute [local irreducible] Janko4.modelGroup

/-- The two word generators have enough distinct row images to reach this order. -/
theorem involutionMatrixLineGenerated_card_ge :
    11520 ≤ Nat.card involutionMatrixLineGenerated := by
  have h0 := LineOverlapCertificate.level0_bound
  have h1 := LineOverlapCertificate.level1_bound
  have hc : Nat.card LineOverlapCertificate.generatedUnits =
      Nat.card involutionMatrixLineGenerated :=
    Subgroup.card_map_of_injective LowerBound.quotientSubgroup.subtype_injective
  rw [hc] at h0
  omega

/-- The line's 231 distinct translates bound its stabilizer from above. -/
theorem involutionMatrixLineStabilizer_card_le :
    Nat.card involutionMatrixLineStabilizer ≤ 11520 := by
  have h := LineOverlapCertificate.line_stabilizer_bound
  rw [involutionMatrixQuotient_card] at h
  omega

/-- The two literal words generate the entire specified line stabilizer. -/
theorem involutionMatrixLineStabilizer_eq_generated :
    involutionMatrixLineStabilizer = involutionMatrixLineGenerated := by
  symm
  exact Subgroup.eq_of_le_of_card_ge LineOverlapCertificate.generated_le_stabilizer
    (involutionMatrixLineStabilizer_card_le.trans involutionMatrixLineGenerated_card_ge)

/-- The exact order, now certified independently of the witness search. -/
theorem involutionMatrixLineStabilizer_card :
    Nat.card involutionMatrixLineStabilizer = 11520 := by
  apply le_antisymm involutionMatrixLineStabilizer_card_le
  rw [involutionMatrixLineStabilizer_eq_generated]
  exact involutionMatrixLineGenerated_card_ge

/-- The full preimage includes every two-core factor, as well as the two lifts. -/
theorem involutionMatrixLine_preimage_eq :
    involutionMatrixLineStabilizer.comap involutionSourceMatrixMap =
      pCore 2 sourceSubgroup ⊔ involutionSourceLineGenerated := by
  rw [involutionMatrixLineStabilizer_eq_generated, involutionMatrixLineGenerated_preimage]

/-- An exact fifteen-membership criterion for placement in an actual max4 conjugate. -/
theorem involutionMatrixLine_preimage_le_iff (g : Janko4.Model) :
    involutionMatrixLineStabilizer.comap involutionSourceMatrixMap ≤
        involutionSourceMax4Overlap g ↔
      (∀ i : Fin 13, involutionSourceCoreGenerator i ∈ involutionSourceMax4Overlap g) ∧
      (∀ i : Fin 2, involutionSourceLineGenerator i ∈ involutionSourceMax4Overlap g) := by
  rw [involutionMatrixLine_preimage_eq, sup_le_iff, involutionSource_twoCore_le_iff,
    involutionSourceLineGenerated, closure_le, Set.range_subset_iff]
  rfl

/-- The full line-stabilizer preimage, including O₂(H), lies in an actual
ATLAS max4 conjugate. -/
theorem involutionMatrixLine_preimage_placement :
    ∃ g : Janko4.Model,
      involutionMatrixLineStabilizer.comap involutionSourceMatrixMap ≤
        involutionSourceMax4Overlap g := by
  obtain ⟨g, hg⟩ := involutionLine_ambient_word_placement
  exact ⟨g, (involutionMatrixLine_preimage_le_iff g).mpr hg⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
