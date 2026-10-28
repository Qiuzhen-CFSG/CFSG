module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.PairOrder
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.SylowCover

/-!
# Elementary-pair incidence in the finite max2 quotient

The fixed words are shared by two independent finite calculations: the Sylow
order and exhaustive double-coset cover, and the memberships and power
obstructions for the representatives. The checked certificates discharge all
five premises of the assembly interface below. Every elementary pair product
has order 2304; Sylow conjugacy and the double-coset obstructions place it in
a conjugate of one of the two concrete candidates.

The source application is Aschbacher–Smith, Proposition 1.3.4, printed
p.511/PDF p.528 of refs/quasithin.pdf.
-/

public section
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Theory.GroupTheory.SubgroupEnumeration

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Assemble the two independent finite certificates for the published words. -/
theorem elementaryMatrixIncidence_of_finiteCertificates
    (hcard : Nat.card FiniteIncidence.baseSubgroup = 256)
    (hcover : DoubleCosetCover FiniteIncidence.baseSubgroup FiniteIncidence.representative)
    (hline : FiniteIncidence.baseSubgroup ≤ involutionMatrixLineStabilizer)
    (hsecond : FiniteIncidence.baseSubgroup ≤ involutionMatrixSecondSubgroup)
    (hrep : ∀ j : Fin 110,
      FiniteIncidence.representative j ∈ involutionMatrixLineStabilizer ∨
      FiniteIncidence.representative j ∈ involutionMatrixSecondSubgroup ∨
      ∃ x ∈ FiniteIncidence.baseSubgroup ⊔ Subgroup.zpowers (FiniteIncidence.representative j),
        x ^ 2304 ≠ 1) :
    ElementaryMatrixIncidence :=
  elementaryMatrixIncidence_of_doubleCosetObstructions
    FiniteIncidence.baseSubgroup FiniteIncidence.representative
    hcard hline hsecond hcover hrep

/-- Every elementary subgroup of order nine that permutes setwise with a Sylow
two-subgroup lies, together with it, in a conjugate of one of the two specified
matrix candidates. All finite certificate premises are discharged. -/
theorem elementaryMatrixIncidence : ElementaryMatrixIncidence :=
  elementaryMatrixIncidence_of_finiteCertificates
    FiniteIncidence.baseSubgroup_card
    FiniteIncidence.representative_doubleCoset_cover
    FiniteIncidence.baseSubgroup_le_line
    FiniteIncidence.baseSubgroup_le_second
    FiniteIncidence.representative_alternatives

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
