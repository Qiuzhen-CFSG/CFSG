module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.JankoTwoHigmanSims.LocalSections

/-!
# The remaining J₂ and HS ambient local-section constructions

A local section with an odd elementary cube supplies the concrete
rank-three witness by lifting through its normal two-group kernel.
The two family producers below concern the native degree-100 J₂ and HS
carriers through the actual full central quotient of L.

This is conditional assembly, not the completed selected-conjugator step.
The local sections have not yet been constructed from `ResidualInputs`.
The actual-model nonfixation in `Sporadic.Actions` supplies neither those
sections nor innerness of the actors. The J₂ full A₅-fixer bound is false
and is not used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.5(8),(10), p.1172; I.2.2(5), pp.409–412; and 16.5.6(3), p.1197.
Final assembly must discharge both family producers, retaining outer
actors and the permitted central covers.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Conditional assembly from the two genuine ambient local-section constructions.
Neither producer is asserted here. The source theorem retains their discharge. -/
theorem jankoTwoHigmanSims_rankWitness_of_localSections
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R)
    (name : ClassificationModels.SporadicName) (hn : IsJankoTwoHigmanSimsName name)
    (e : (L ⧸ center L) ≃* name.Carrier)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    (j2 : Hypothesis1611 KnownSimple.IsKnownSimple G → ResidualInputs T z L g R →
      ∀ _e : (L ⧸ center L) ≃* _root_.Sporadic.LeechRelated.J2.Carrier,
        modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
          modifiedCentralizerResidual L (MulAut.conj g z) →
        JankoTwoHigmanSims.HasLocalSection G)
    (hs : Hypothesis1611 KnownSimple.IsKnownSimple G → ResidualInputs T z L g R →
      ∀ _e : (L ⧸ center L) ≃* _root_.Sporadic.LeechRelated.HS.Carrier,
        modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
          modifiedCentralizerResidual L (MulAut.conj g z) →
        JankoTwoHigmanSims.HasLocalSection G) :
    Nonempty (OddRankThreeWitness G) := by
  rcases hn with rfl | rfl
  · exact JankoTwoHigmanSims.rankWitness_of_local_section (j2 hG d e hne)
  · exact JankoTwoHigmanSims.rankWitness_of_local_section (hs hG d e hne)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic
