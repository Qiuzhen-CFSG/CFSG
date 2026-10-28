module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.NormalSeed.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Complete.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime

/-!
# Completion of the non-Bender centralizer branch

The original normal-seed argument now gives Suzuki recognition from its
rank obstruction. The proved diagonal parabolic and moved odd-prime
generation theorem discharge the other source premises. Applying the
existing non-Bender argument therefore excludes the absence of an escaping
Bender component in the original involution centralizer.

The wreath and replacement applications retain precisely their independent
Bender-recognition, geometry and overgroup premises. Their final discharge
belongs to the wreath-recognition and linear-three replacement owners;
no H-star quotient recognition or Hall faithfulness is asserted here.

Source: Aschbacher--Smith, 10.3.3, printed p.756, using 10.2.4, p.747.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
variable {G : Type*} [Group G] [Finite G]

/-- The original normal-seed contract with its earlier parabolic input discharged. -/
theorem normalSeedBender (T : Sylow 2 G) : NormalSeedBenderAt T :=
  normalSeedBender_of_parabolicSeed (Overgroups.Closure.Parabolic.parabolicSeed T)

/-- The exact non-Bender contract, with every source input discharged. -/
theorem nonBenderGeneration (T : Sylow 2 G) : NonBenderGenerationAt T :=
  nonBenderGeneration_of_remaining (normalSeedBender T)
    (Overgroups.Closure.Parabolic.parabolicSeed T)
    Overgroups.ModelGeneration.movedOddPrimeGeneration

/-- The actual wreath consumer now needs only its independent Bender branch. -/
theorem wreathRecognition_of_bender {T : Sylow 2 G} (hB : BenderRecognitionAt T) :
    WreathRecognitionAt T :=
  wreathRecognition_of_branches hB (nonBenderGeneration T)

/-- Application to the original replacement contract, preserving its other source branches. -/
theorem replacement_of_bender {T : Sylow 2 G}
    (hgeometry : CentralizerGeometryAt T) (hB : BenderRecognitionAt T)
    (hovergroups : OvergroupSpanAt T) : SourceLinearThreeReplacementAt T :=
  replacement_of_wreath_branches hgeometry hB (nonBenderGeneration T) hovergroups

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
