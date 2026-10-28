module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Complete
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.LocalSource

/-!
# The actual centralizer wreath quotient

The nonnormal Hall-faithfulness theorem discharges the last input to the
Bender branch. Together with the completed non-Bender exclusion, this gives
the actual isomorphism K_z T / O₂(K_z T) ≃ S₅ wr C₂, the strict containment
O²(C_{L₀}(z)) < K_z, escape from M, and every C-component orbit equality.
The original survivor, centralizer data and multiple-overgroup guard remain
the hypotheses of the source contract.

The literal replacement application below discharges wreath recognition.
Centralizer geometry and the overgroup span identity remain separate inputs
to that construction, whose final assembly belongs to the linear-three
replacement theorem.

Source: Aschbacher--Smith, 10.3.3 and its application, printed pp.756--757,
using 10.2.3(2) and 10.2.4, pp.745,747.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
variable {G : Type*} [Group G] [Finite G]

/-- The Bender branch with Hall faithfulness and both recognition inputs proved. -/
theorem Bender.benderRecognition (T : Sylow 2 G) : BenderRecognitionAt T :=
  Bender.benderRecognition_of_hall source_nonnormalHallFaithful

/-- Original 10.3.3 on the supplied centralizer data, including the literal
two-residual and every component-orbit conclusion, with all branch inputs proved. -/
theorem wreathRecognition (T : Sylow 2 G) : WreathRecognitionAt T :=
  Bender.wreathRecognition_of_hall source_nonnormalHallFaithful

/-- The actual A₅ replacement construction now retains only the independent
centralizer-geometry and overgroup-span source inputs. -/
theorem replacement_of_geometry_and_overgroups {T : Sylow 2 G}
    (hgeometry : CentralizerGeometryAt T) (hovergroups : OvergroupSpanAt T) :
    SourceLinearThreeReplacementAt T :=
  replacement_of_source_inputs hgeometry (wreathRecognition T) hovergroups

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
