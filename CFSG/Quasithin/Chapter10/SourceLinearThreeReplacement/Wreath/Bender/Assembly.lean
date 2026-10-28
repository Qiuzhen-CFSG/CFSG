module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Hall
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Orbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Assembly

/-!
# Conditional assembly of the source Bender branch

The Borel theorem supplies the actual H-star subgroup I T. Reselection
applies the independent Hall-faithfulness theorem. The parabolic theorem
then supplies the wreath quotient and the nontrivial two-residual seed
inside I T. Relative normality and component conjugacy identify its whole
centralizer span, giving exactly the quotient and orbit in BenderRecognitionAt.

The two source inputs and Hall faithfulness remain explicit obligations;
this assembly is not an unconditional proof of 10.3.3.
Source: Aschbacher--Smith, 10.2.3 and 10.3.3, pp.744--745,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The remaining independent inputs imply the exact existing branch contract. -/
theorem benderRecognition_of_source_inputs (hBorel : BorelHStarAt T)
    (hfaith : SourceNonnormalHallFaithfulAt T) (hrecognition : HStarRecognitionAt T) :
    BenderRecognitionAt T := by
  intro hmany L D s d I hI hout hb
  have hH := hBorel hmany L D s d I hI hout hb
  have hf : HallFaithful D (I ⊔ (T : Subgroup G)) :=
    fun B hBM hB hab hperm => survivor_hall_faithful hfaith hmany s hH B hBM hB hab hperm
  obtain ⟨⟨e⟩,hX,hne⟩ := hrecognition hmany L D s d (I ⊔ (T : Subgroup G)) hH
    (sup_le hI.1 d.sylow_le_centralizer) hf
  exact recognition_of_join d hI e hX hne

/-- Connect the independent Bender source inputs to the existing replacement consumer. -/
theorem replacement_of_bender_inputs (hgeometry : CentralizerGeometryAt T)
    (hBorel : BorelHStarAt T) (hfaith : SourceNonnormalHallFaithfulAt T)
    (hrecognition : HStarRecognitionAt T) (hN : NonBenderGenerationAt T)
    (hovergroups : OvergroupSpanAt T) : SourceLinearThreeReplacementAt T :=
  replacement_of_wreath_branches hgeometry
    (benderRecognition_of_source_inputs hBorel hfaith hrecognition) hN hovergroups

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
