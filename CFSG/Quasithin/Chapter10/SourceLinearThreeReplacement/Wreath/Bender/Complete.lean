module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Parabolic.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Borel.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Complete

/-!
# Wreath recognition with only the independent Hall source input

The Borel source theorem and the H-star parabolic recognition theorem
now discharge both local Bender inputs. The completed non-Bender branch
then gives the original wreath contract, including the literal residual
and every component-orbit equality. The final replacement application
retains its separate centralizer-geometry and overgroup-span inputs.

The remaining Hall-faithfulness premise is owned by
qt-d-10-nona5-hall-faithfulness. Its discharge in the wreath contract
remains with qt-d-10-replacement-wreath-recognition; the complete replacement
assembly belongs to qt-d-10-linear-three-replacement. These are conditional
source applications, not unconditional proofs of 10.3.3.
Source: Aschbacher--Smith, 10.2.3 and 10.3.3, pp.744--745,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Both local Bender branches are discharged; only the independent Hall
source theorem remains. -/
theorem benderRecognition_of_hall (hfaith : SourceNonnormalHallFaithfulAt T) :
    BenderRecognitionAt T :=
  benderRecognition_of_source_inputs borelHStar_source hfaith (Parabolic.hstarRecognition T)

/-- The original actual wreath quotient and all component-orbit conclusions. -/
theorem wreathRecognition_of_hall (hfaith : SourceNonnormalHallFaithfulAt T) :
    WreathRecognitionAt T :=
  NonBender.wreathRecognition_of_bender (benderRecognition_of_hall hfaith)

/-- The actual replacement consumer with all local wreath obligations discharged. -/
theorem replacement_of_hall
    (hgeometry : CentralizerGeometryAt T) (hfaith : SourceNonnormalHallFaithfulAt T)
    (hovergroups : OvergroupSpanAt T) : SourceLinearThreeReplacementAt T :=
  NonBender.replacement_of_bender hgeometry (benderRecognition_of_hall hfaith) hovergroups

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
