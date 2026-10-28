module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.Actions

/-!
# Assembly of the sporadic selected-residual constructions

The three independent branches cover exactly M₁₁, M₁₂, M₂₂, M₂₃, M₂₄,
J₂, HS, J₄ and Ru. E1 supplies the genuine central quotient equivalence
from the E2 two-core quotient equivalence; no central covering kernel is
discarded. The supporting action module proves that unequal residuals
remain distinct in this model and that the inverse involution moves an
odd-order element of the actual residual image.

The theorem here is conditional assembly only. The three family producers
must still construct the ambient nontrivial two-subgroup, elementary
odd-prime plane and independent commuting prime-order element. Neither
the centralizer tables nor abstract residual isomorphisms discharge them.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
E2(iii), 16.1.2 and 16.1.5, printed pp.1170–1172; I.2.2, pp.409–412;
and the selected-conjugator step of 16.5.6(3), p.1197.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Conditional assembly across the exact nine sporadics. Every producer
retains the selected conjugator, actual residuals and full covering component.
The family constructions are still separate mathematical obligations. -/
theorem rankWitness_of_families
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R)
    (hL : IsEvenTypeSporadicQuotient (L ⧸ pCore 2 L))
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    (hMathieu : ∀ name : ClassificationModels.SporadicName, IsMathieuName name →
      (L ⧸ center L ≃* name.Carrier) →
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
        modifiedCentralizerResidual L (MulAut.conj g z) → Nonempty (OddRankThreeWitness G))
    (hJ2HS : ∀ name : ClassificationModels.SporadicName, IsJankoTwoHigmanSimsName name →
      (L ⧸ center L ≃* name.Carrier) →
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
        modifiedCentralizerResidual L (MulAut.conj g z) → Nonempty (OddRankThreeWitness G))
    (hJ4Ru : ∀ name : ClassificationModels.SporadicName, IsJankoFourRudvalisName name →
      (L ⧸ center L ≃* name.Carrier) →
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
        modifiedCentralizerResidual L (MulAut.conj g z) → Nonempty (OddRankThreeWitness G)) :
    Nonempty (OddRankThreeWitness G) := by
  obtain ⟨name, hj3, hhe, ⟨e⟩⟩ := hL
  let eZ := centralModelEquiv hG d e
  rcases name_cases hj3 hhe with hm | hj | hr
  · exact hMathieu name hm eZ hne
  · exact hJ2HS name hj eZ hne
  · exact hJ4Ru name hr eZ hne

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic
